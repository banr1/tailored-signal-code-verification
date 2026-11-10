/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudget
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Code-Loaded Placed Budget Step Lemmas for `Unchunked.Ct1Sent::merge` (Block `312`)

Re-exports the `withLsCodeRoLoaded lsmpl` budget-threaded exit and per-field step lemmas for
`Unchunked.Ct1Sent::merge` on Block `312`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepClPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl blkPC_312 blkPl_312)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint mergeBytes skipField)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix sliceCursorAfter)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost authenticatorPBCapAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (HighCalleeSaved24 SepWPpLscro codecWireTypeToProto unchunkedMergeBelow vecU8CapAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge (UnchunkedCt1SentMergeGhost)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofBudget (bytesMerge3RawSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (UnchunkedCt1SentMergeEnv decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit (WppPanicFalse spqrPoolAt)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedBaseBudget
  (unchunkedCt1SentMergeOwnSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudgetAux
  (ct1SentErrFrame ct1SentLoopPre unchunkedSavedRegs)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

theorem ct1Sent_from_err_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {kindTag : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f + 1 ≤ 4 * x.bs.length + 8)
    (hnoheap : KindNoHeap kindTag)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_312).base + 108#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 112#64) ↦₆₄ kindTag) ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ct1SentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudgetAux.ct1Sent_from_err_exit_cl_placed
    hFromCall hFit hnone hf hnoheap hsp_align hpc hrun hsp htr hcs

theorem ct1Sent_push_err_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f + 1 ≤ 4 * x.bs.length + 8)
    (herr : err ≠ 0#64)
    (hn : n ≤ 1)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_312).base + 712#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 112#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 112#64) ↦₆₄ err) ∗
        decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ct1SentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudgetAux.ct1Sent_push_err_exit_cl_placed
    hPushCall hFit hnone hf herr hn hsp_align hpc hrun hsp htr hx0 hcs

theorem ct1Sent_skip_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_312).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s'
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 404#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (ct1SentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudgetAux.ct1Sent_skip_step_cl_placed
    hSkipCall hFit hsp_align hrest_le hrest_lt hrest_suf htag_lt hnone_of_sf hcont
    hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hcs

theorem ct1Sent_tag1_push_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {err : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f + 1 ≤ 4 * x.bs.length + 8)
    (herr : err ≠ 0#64)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_312).base + 552#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 112#64) ↦₆₄ err) ∗
        decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ct1SentErrFrame A lim st f s0 s x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudgetAux.ct1Sent_tag1_push_exit_cl_placed
    hPushCall hFit hnone hf herr hsp_align hpc hrun hsp htr hcs

theorem ct1Sent_tag1_wt_err_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {iwt : WireType}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hiwt : iwt ≠ .varint)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hpc : s.pc = (blkPl_312).base + 372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (ct1SentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudgetAux.ct1Sent_tag1_wt_err_step_cl_placed
    hFromCall hPushCall hFit hiwt hsp_align hrest_le hrest_suf hnone hpc hrun hsp htr hx0 hcs

theorem ct1Sent_tag1_varint_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_312).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s'
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with epoch := v } x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 (WireType.varint).toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (ct1SentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudget.ct1Sent_tag1_varint_step_cl_placed
    hPushCall hVarintCall hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_dv hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hcs

theorem ct1Sent_tag2_call_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hAuthCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_am : (mergeMessage ProtoAuthenticator.mergeField
      (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = none →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage ProtoAuthenticator.mergeField
        (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = some (v, rest') →
      s'.pc = (blkPl_312).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s'
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with auth := some v } x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 300#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (spqrPoolAt A lim st (4 * (x.bs.length - rest.length)) x.bs.length 0 s ∗
        vecU8CapAt A.repAlloc x.msgPtr rest.length m.hdr ∗
        vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) rest.length m.es ∗
        vecU8CapAt A.repAlloc (x.msgPtr + 0x30#64) rest.length m.ct1 ∗
        authenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) rest.length (m.auth.getD default) ∗
        ((x.msgPtr + 0x78#64) ↦₆₄ m.epoch) ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗
        memRegion (s0.sp - 112#64) 48 ∗
        unchunkedSavedRegs s0.sp s0 ∗
        unchunkedMergeBelow s0.sp)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudget.ct1Sent_tag2_call_step_cl_placed
    hPushCall hAuthCall hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_am hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hcs

theorem ct1Sent_tag2_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hAuthCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_am : (mergeMessage ProtoAuthenticator.mergeField
      (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = none →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage ProtoAuthenticator.mergeField
        (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = some (v, rest') →
      s'.pc = (blkPl_312).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s'
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with auth := some v } x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 276#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (ct1SentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudget.ct1Sent_tag2_step_cl_placed
    hPushCall hAuthCall hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_am hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hcs

theorem ct1Sent_tag3_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_312).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s'
        (ct1SentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with hdr := v } x.bs rest')
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 324#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (ct1SentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
      (WppPanicFalse R) :=
  LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudget.ct1Sent_tag3_step_cl_placed
    hPushCall hBytesCall hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_mb hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hcs

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepClPlacedBudget
