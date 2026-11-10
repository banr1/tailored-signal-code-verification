/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudget
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Code-Loaded Placed Budget Inner `Unchunked.EkSent` Lemmas for `Chunked.HeaderSent::merge` (Block `302`)

Re-exports the `withLsCodeRoLoaded lsmpl` budget-threaded inner `Unchunked.EkSent` loop and
decode-error exit lemmas for `Chunked.HeaderSent::merge` on Block `302`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcClPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint mergeBytes skipField)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder PolynomialEncoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedHeaderSentMergeGhost ChunkedInl10CalleeSaved SepWPpLscro
   blkPC_302 blkPl_302 chunkedInlBelowStack codecWireTypeToProto mergeLoopBin)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedHeaderSentMergeEnv chunkedHeaderSentMergeSpec headerSentPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit (WppPanicFalse)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudgetAux
  (chunkedHeaderSentErrFrame chunkedHeaderSentLoopPre chunkedHeaderSentUcLoopPre
   chunkedHeaderSent_from_err_exit_placed chunkedHeaderSent_push_ret_exit_placed
   chunkedHeaderSent_uc_field_push_exit_placed chunkedHeaderSent_uc_from_push_exit_placed
   chunkedHeaderSent_uc_loop_le_exit_placed chunkedHeaderSent_uc_push_exit_placed
   chunkedHeaderSent_uc_tag1_wt_err_step_placed chunkedHeaderSent_uc_tag2_step_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (bytesMerge3RawBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

theorem chunkedHeaderSent_from_err_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.HeaderSent} {s : State} {w : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hnone : (mergeMessage
      V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 1 ≤ 6 * x.bs.length + 12)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_302).base + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedHeaderSentErrFrame A lim st f (headerSentPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedHeaderSent_from_err_exit_placed _ M A lim H hFromCall x st R s0 m s w f
    hFit hnone hf hw hsp_align hpc hrun hsp htr hcs

theorem chunkedHeaderSent_push_ret_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.HeaderSent} {s : State} {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hnone : (mergeMessage
      V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 1 ≤ 6 * x.bs.length + 12)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_302).base + 824#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedHeaderSentErrFrame A lim st f (headerSentPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedHeaderSent_push_ret_exit_placed _ M A lim H hPushCall x st R s0 m s err n f
    hFit hnone hf hn herr hsp_align hpc hrun hsp htr hx0 hcs

theorem chunkedHeaderSent_uc_push_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.HeaderSent} {s : State} {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hnone : (mergeMessage
      V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 1 ≤ 6 * x.bs.length + 12)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_302).base + 792#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        memRegion (s0.sp - 128#64) 48 ∗
        chunkedHeaderSentErrFrame A lim st f (headerSentPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedHeaderSent_uc_push_exit_placed _ M A lim H hPushCall x st R s0 m s err n f
    hFit hnone hf hn herr hsp_align hpc hrun hsp htr hx1 hcs

theorem chunkedHeaderSent_uc_from_push_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.HeaderSent} {s : State} {w : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hnone : (mergeMessage
      V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 2 ≤ 6 * x.bs.length + 12)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_302).base + 780#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedHeaderSentErrFrame A lim st f (headerSentPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedHeaderSent_uc_from_push_exit_placed _ M A lim H hFromCall hPushCall x st R s0 m s w f
    hFit hnone hf hw hsp_align hpc hrun hsp htr hcs

theorem chunkedHeaderSent_uc_field_push_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.HeaderSent} {s : State} {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hnone : (mergeMessage
      V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 2 ≤ 6 * x.bs.length + 12)
    (hn : n ≤ 1) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_302).base + 1072#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedHeaderSentErrFrame A lim st f (headerSentPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedHeaderSent_uc_field_push_exit_placed _ M A lim H hPushCall x st R s0 m s err n f
    hFit hnone hf hn herr hsp_align hpc hrun hsp htr hx0 hcs

theorem chunkedHeaderSent_uc_skip_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hSkipCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder}
    {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_302).base + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          uc sendingEk receivingCt1 x.bs rest' (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 540#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        uc sendingEk receivingCt1 x.bs rest (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudget.chunkedHeaderSent_uc_skip_step_cl_placed
    _ M A lim H hPushCall hSkipCall x st R s0 s uc sendingEk receivingCt1 rest iwt tag outerLimit innerLimit
    hFit hsp_align hrest_le hrest_lt hrest_suf htag_lt hnone_of_sf hcont
    hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs

theorem chunkedHeaderSent_uc_tag1_varint_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder}
    {rest : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_302).base + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc with epoch := v } sendingEk receivingCt1 x.bs rest' (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 604#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        uc sendingEk receivingCt1 x.bs rest (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudget.chunkedHeaderSent_uc_tag1_varint_step_cl_placed
    _ M A lim H hPushCall hVarintCall x st R s0 s uc sendingEk receivingCt1 rest outerLimit innerLimit
    hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_dv hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs

theorem chunkedHeaderSent_uc_tag1_wt_err_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder}
    {rest : List (BitVec 8)} {iwt : WireType}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hiwt : iwt ≠ .varint) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (mergeMessage
      V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hpc : s.pc = (blkPl_302).base + 604#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        uc sendingEk receivingCt1 x.bs rest (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedHeaderSent_uc_tag1_wt_err_step_placed _ M A lim H hFromCall hPushCall x st R s0 s
    uc sendingEk receivingCt1 rest iwt hFit hiwt hsp_align hrest_le hrest_suf hnone hpc hrun hsp htr hx0 hcs

theorem chunkedHeaderSent_uc_tag2_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hAuthCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder}
    {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_auth : (mergeMessage
        ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = none →
      (mergeMessage
        V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (auth' : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage
        ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = some (auth', rest') →
      s'.pc = (blkPl_302).base + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc with auth := some auth' } sendingEk receivingCt1 x.bs rest' (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 560#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        uc sendingEk receivingCt1 x.bs rest (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedHeaderSent_uc_tag2_step_placed _ M A lim H hPushCall hAuthCall x st R s0 s
    uc sendingEk receivingCt1 rest iwt outerLimit innerLimit hFit hsp_align hrest_le hrest_lt hrest_suf
    hnone_of_auth hcont hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs

theorem chunkedHeaderSent_uc_tag3_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder}
    {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_302).base + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc with dk := v } sendingEk receivingCt1 x.bs rest' (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 440#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        uc sendingEk receivingCt1 x.bs rest (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudget.chunkedHeaderSent_uc_tag3_step_cl_placed
    _ M A lim H hPushCall hBytesCall x st R s0 s uc sendingEk receivingCt1 rest iwt outerLimit innerLimit
    hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_mb hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs

theorem chunkedHeaderSent_uc_loop_le_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hle_lim : cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hlim_lt : innerLimit < 2 ^ 63)
    (hnone_of_lt : cur.length < innerLimit →
      (mergeMessage
        V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (s' : State),
      cur.length = innerLimit →
      s'.pc = (blkPl_302).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs cur (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 464#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        uc sendingEk receivingCt1 x.bs cur (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedHeaderSent_uc_loop_le_exit_placed _ M A lim H hFromCall hPushCall x st R s0 s
    uc sendingEk receivingCt1 cur outerLimit innerLimit hFit hle_lim hsp_align hcur_le hcur_suf hlim_lt
    hnone_of_lt hcont hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs

theorem chunkedHeaderSent_uc_decode_key_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hgt_lim : ¬ cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hnone_of_uc_none :
      mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
      (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_302).base + 516#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          uc sendingEk receivingCt1 x.bs rest (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 464#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        uc sendingEk receivingCt1 x.bs cur (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudget.chunkedHeaderSent_uc_decode_key_step_cl_placed
    _ M A lim H hFromCall hPushCall hVarintCall x st R s0 s uc sendingEk receivingCt1 cur outerLimit innerLimit
    hFit hgt_lim hsp_align hcur_le hcur_lt hcur_suf hnone_of_uc_none hcont
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs

theorem chunkedHeaderSent_uc_loop_ok_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {sendingEk : Option PolynomialEncoder} {receivingCt1 : Option PolynomialDecoder}
    {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : innerLimit < 2 ^ 63) :
    ∀ (n : Nat) (uc : V1State.Unchunked.EkSent) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (∀ (uc' : V1State.Unchunked.EkSent) (rest' : List (BitVec 8)) (s' : State),
        rest'.length = innerLimit → rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
        mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = some uc' →
        s'.pc = (blkPl_302).base + 168#64 →
        s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
        s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
        s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
        s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
        s'.readReg64 (Reg.gpr 25#5) = 8#64 → ChunkedInl10CalleeSaved s0 s' →
        SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
          (chunkedHeaderSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
            { uc := some uc', sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs rest' (headerSentPolyCapBound x))
          (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R)) →
      (mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
        (mergeMessage V1State.Chunked.HeaderSent.mergeField
          (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) →
      s.pc = (blkPl_302).base + 464#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s.readReg64 (Reg.gpr 25#5) = 8#64 → s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
        (chunkedHeaderSentUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
          uc sendingEk receivingCt1 x.bs cur (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudget.chunkedHeaderSent_uc_loop_ok_cl_placed
    _ M A lim H hFromCall hPushCall hVarintCall hSkipCall hAuthCall hBytesCall
    x st R s0 sendingEk receivingCt1 outerLimit innerLimit hFit hsp_align hbs_lt hlim_lt

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcClPlacedBudget
