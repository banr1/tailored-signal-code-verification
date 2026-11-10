/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonClPlaced

/-!
# Code-Loaded Placed Budget Exit & Skip Lemmas for `PolynomialDecoder::merge` (Block `296`)

Proves envelope-parameterized (`*_ofEnv`) and `polyDecoderMergeSpec`-specialized code-loaded
`[LibsignalPlacement]` exit and unknown-tag skip lemmas for `PolynomialDecoder::merge` on Block `296`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonClPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec (WireType skipField)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (PolyCalleeSaved PolyDecoderMergeGhost WppPost blkPC_296 blkPl_296 codecWireTypeToProto
   polyBelowStack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (DecodeErrorPushMergeEnv decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (FitsEnv.polyMergeLoop_head FitsEnv.polyMergeLoop_mono PolyDecoderMergePostEnv PolyMergeIterEnv
   PolyMergeLoopEnv WppBudgetPanic polyDecoderCapBound polyDecoderErrFrame polyDecoderLoopPre
   polyDecoderMergeSpec polyDecoderMergeSpecOfEnv polyDecoder_err0_ret_exit_placed
   polyDecoder_from_err_exit_placed polyDecoder_push_err_exit_placed polyDecoder_skip_step_placed)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (SkipField3Env skipField3Spec)

/-! ## 1. Envelope-Parameterized Code-Loaded Exit & Skip Lemmas (`OfEnv`) -/

/-- Envelope-parameterized placed shared exit from `+0x07c` (`(blkPl_296).base + 124#64`). -/
theorem polyDecoder_err0_ret_exit_cl_placed_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyDecoderMergeGhost → List AllocEvent → Prop}
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {err : BitVec 64}
    (hnone : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hevs : ∃ evs, PostEnv x evs ∧ st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_296).base + 124#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = err) (herr : err ≠ 0#64) (hcs : PolyCalleeSaved s0 s) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err 0 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 48 ∗
        polyDecoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) :=
  polyDecoder_err0_ret_exit_placed hnone hevs hsp_align hpc hrun hsp htr hx1 herr hcs

/-- Envelope-parameterized code-loaded shared exit from `+0x070` (`(blkPl_296).base + 112#64`)
calling `DecodeError::from` (`261`). -/
theorem polyDecoder_from_err_exit_cl_placed_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyDecoderMergeGhost → List AllocEvent → Prop}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {w : BitVec 64}
    (hnone : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hw : KindNoHeap w)
    (hfits_from : FitsEnv M lim st_cur DecodeErrorFromEnv)
    (hevs_from : ∀ evs_f, DecodeErrorFromEnv evs_f →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_f st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_296).base + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗
        polyDecoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) :=
  polyDecoder_from_err_exit_placed hFromCall hnone hw hfits_from hevs_from hsp_align
    hpc hrun hsp htr hcs hinv

/-- Envelope-parameterized code-loaded shared exit from `+0x380` (`(blkPl_296).base + 896#64`)
calling `DecodeError::push` (`257`). -/
theorem polyDecoder_push_err_exit_cl_placed_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyDecoderMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {err : BitVec 64}
    (hnone : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64)
    (hfits_push : FitsEnv M lim st_cur (DecodeErrorPushMergeEnv 0))
    (hevs_push : ∀ evs_p, DecodeErrorPushMergeEnv 0 evs_p →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_p st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_296).base + 896#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗
        polyDecoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) :=
  polyDecoder_push_err_exit_placed hPushCall hnone herr hfits_push hevs_push hsp_align
    hpc hrun hsp htr hx0 hcs hinv

/-- Envelope-parameterized code-loaded step lemma for unknown field tags (`tag ∉ {1, 2, 3, 4}`) at
`+0x140` (`(blkPl_296).base + 320#64`) calling `skip_field` (`263`). -/
theorem polyDecoder_skip_step_cl_placed_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyDecoderMergeGhost → List AllocEvent → Prop}
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hfits_sf : FitsEnv M lim st_cur
      (SkipField3Env ⟨iwt, tag, 97, x.bufRef, x.slot, x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩))
    (hevs_sf_err : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      ∀ evs_sf,
        SkipField3Env ⟨iwt, tag, 97, x.bufRef, x.slot, x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_sf →
        ∃ evs, PostEnv x evs ∧ M.stepEvents evs_sf st_cur = M.stepEvents evs st0)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_296).base + 320#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) :=
  polyDecoder_skip_step_placed hSkipCall hsp_align hrest_le hrest_lt hrest_suf htag_lt
    hfits_sf hevs_sf_err hnone_of_sf hcont hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24
    hcs hinv

/-! ## 2. Concrete `polyDecoderMergeSpec` Code-Loaded Exit & Skip Lemmas -/

private theorem polyDecoderMergePostEnv_of_none {x : PolyDecoderMergeGhost} {f : Nat}
    {evs : List AllocEvent}
    (hnone : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f ≤ 2 * x.bs.length + 2)
    (hevs : PolyMergeLoopEnv f x.bs.length (polyDecoderCapBound x) evs) :
    PolyDecoderMergePostEnv x evs := by
  dsimp only [PolyDecoderMergePostEnv]
  rw [hnone]
  exact hevs.mono_fuel hf

/-- Code-loaded placed shared exit from `+0x07c` (`(blkPl_296).base + 124#64`) for
`polyDecoderMergeSpec`. -/
theorem polyDecoder_err0_ret_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {err : BitVec 64}
    {f_acc : Nat} {evs_acc : List AllocEvent}
    (hnone : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf_acc : f_acc ≤ 2 * x.bs.length + 2)
    (hevs_acc : PolyMergeLoopEnv f_acc x.bs.length (polyDecoderCapBound x) evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_296).base + 124#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = err) (herr : err ≠ 0#64) (hcs : PolyCalleeSaved s0 s) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err 0 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 48 ∗
        polyDecoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  polyDecoder_err0_ret_exit_placed hnone
    ⟨evs_acc, polyDecoderMergePostEnv_of_none hnone hf_acc hevs_acc, hst_cur⟩
    hsp_align hpc hrun hsp htr hx1 herr hcs

/-- Code-loaded placed shared exit from `+0x070` (`(blkPl_296).base + 112#64`): calls
`DecodeError::from` (`261`) and closes `polyDecoderMergeSpec`. -/
theorem polyDecoder_from_err_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {w : BitVec 64}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent}
    (hnone : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hw : KindNoHeap w)
    (hf_rem : 1 ≤ f_rem)
    (hf_tot : f_acc + 1 ≤ 2 * x.bs.length + 2)
    (hevs_acc : PolyMergeLoopEnv f_acc x.bs.length (polyDecoderCapBound x) evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hfits_rem : FitsEnv M lim st_cur
      (PolyMergeLoopEnv f_rem x.bs.length (polyDecoderCapBound x)))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_296).base + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗
        polyDecoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) := by
  have hfits1 : FitsEnv M lim st_cur
      (PolyMergeLoopEnv 1 x.bs.length (polyDecoderCapBound x)) :=
    FitsEnv.polyMergeLoop_mono hf_rem (Nat.le_refl _) (Nat.le_refl _) hfits_rem
  refine polyDecoder_from_err_exit_placed hFromCall hnone hw
    (FitsEnv.polyMergeLoop_head (fuel := 0) (fun _ => PolyMergeIterEnv.of_decodeErrorFrom) hfits1)
    (fun evs_f hf =>
      ⟨evs_acc ++ evs_f,
       polyDecoderMergePostEnv_of_none hnone hf_tot
         (hevs_acc.append (PolyMergeLoopEnv.single (fuel := 0) (PolyMergeIterEnv.of_decodeErrorFrom hf))),
       by rw [hst_cur, ← AllocCostModel.stepEvents_append]⟩)
    hsp_align hpc hrun hsp htr hcs hinv

/-- Code-loaded placed shared exit from `+0x380` (`(blkPl_296).base + 896#64`): calls
`DecodeError::push` (`257`) and closes `polyDecoderMergeSpec`. -/
theorem polyDecoder_push_err_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {err : BitVec 64}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent}
    (hnone : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64)
    (hf_rem : 1 ≤ f_rem)
    (hf_tot : f_acc + 1 ≤ 2 * x.bs.length + 2)
    (hevs_acc : PolyMergeLoopEnv f_acc x.bs.length (polyDecoderCapBound x) evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hfits_rem : FitsEnv M lim st_cur
      (PolyMergeLoopEnv f_rem x.bs.length (polyDecoderCapBound x)))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_296).base + 896#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗
        polyDecoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) := by
  have hfits1 : FitsEnv M lim st_cur
      (PolyMergeLoopEnv 1 x.bs.length (polyDecoderCapBound x)) :=
    FitsEnv.polyMergeLoop_mono hf_rem (Nat.le_refl _) (Nat.le_refl _) hfits_rem
  refine polyDecoder_push_err_exit_placed hPushCall hnone herr
    (FitsEnv.polyMergeLoop_head (fuel := 0) (fun _ => PolyMergeIterEnv.of_decodeErrorPush0) hfits1)
    (fun evs_p hp =>
      ⟨evs_acc ++ evs_p,
       polyDecoderMergePostEnv_of_none hnone hf_tot
         (hevs_acc.append (PolyMergeLoopEnv.single (fuel := 0) (PolyMergeIterEnv.of_decodeErrorPush0 hp))),
       by rw [hst_cur, ← AllocCostModel.stepEvents_append]⟩)
    hsp_align hpc hrun hsp htr hx0 hcs hinv

/-- Code-loaded placed step lemma for unknown field tags (`tag ∉ {1, 2, 3, 4}`) at `+0x140`
(`(blkPl_296).base + 320#64`) for `polyDecoderMergeSpec`. -/
theorem polyDecoder_skip_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hf_rem : 1 ≤ f_rem)
    (hf_tot : f_acc + 1 ≤ 2 * x.bs.length + 2)
    (hevs_acc : PolyMergeLoopEnv f_acc x.bs.length (polyDecoderCapBound x) evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hfits_rem : FitsEnv M lim st_cur
      (PolyMergeLoopEnv f_rem x.bs.length (polyDecoderCapBound x)))
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0))
    (hpc : s.pc = (blkPl_296).base + 320#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) := by
  have hfits1 : FitsEnv M lim st_cur
      (PolyMergeLoopEnv 1 x.bs.length (polyDecoderCapBound x)) :=
    FitsEnv.polyMergeLoop_mono hf_rem (Nat.le_refl _) (Nat.le_refl _) hfits_rem
  refine polyDecoder_skip_step_placed hSkipCall hsp_align hrest_le hrest_lt hrest_suf htag_lt
    (FitsEnv.polyMergeLoop_head (fuel := 0) (fun _ => PolyMergeIterEnv.of_skipField3) hfits1)
    (fun hsf evs_sf hsf_ev =>
      ⟨evs_acc ++ evs_sf,
       polyDecoderMergePostEnv_of_none (hnone_of_sf hsf) hf_tot
         (hevs_acc.append (PolyMergeLoopEnv.single (fuel := 0) (PolyMergeIterEnv.of_skipField3 hsf_ev))),
       by rw [hst_cur, ← AllocCostModel.stepEvents_append]⟩)
    hnone_of_sf hcont hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hcs hinv

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonClPlacedBudget
