/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderStepClPlacedBudget

/-!
# Code-Loaded Placed Budget Verification of `PolynomialEncoder::merge` (Block `297`)

Exports the `withLsCodeRoLoaded` and `withLsCodeLoaded` `[LibsignalPlacement]` loop and top-level
budget contracts (`polyEncoderMerge_cro_placed_ok_of_contracts`,
`polyEncoderMerge_cl_placed_ok_of_contracts`) for `PolynomialEncoder::merge` on Block `297`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (PolyCalleeSaved PolyEncoderMergeGhost WppPost blkPC_297 blkPl_297 codecWireTypeToProto
   mergeLoopBin)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyEncoderMergeEnv PolyMergeLoopEnv WppBudgetPanic bytesMerge3RawBudgetSpec
   polyEncoderCapBound polyEncoderLoopPre polyEncoderMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

/-! ## 1. Code-RO-Loaded Loop Exit, Key Decode, Loop Induction & Top-Level Contract -/

/-- Code-loaded placed budget loop exit lemma at `+0x0a4` (`(blkPl_297).base + 164#64`) when
`cur.length ≤ limit`. -/
theorem polyEncoder_loop_le_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {cur : List (BitVec 8)} {limit : Nat}
    {evs_acc : List AllocEvent} :
    cur.length ≤ limit → (s0.sp &&& 15#64 == 0#64) = true →
    cur.length ≤ x.bs.length → IsDropSuffix x.bs cur → limit < 2 ^ 63 →
    PolyMergeLoopEnv (2 * (x.bs.length - cur.length)) x.bs.length
      (polyEncoderCapBound x) evs_acc →
    st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur
      (PolyMergeLoopEnv (2 * cur.length + 2) x.bs.length (polyEncoderCapBound x)) →
    (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin PolynomialEncoder.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
    s.pc = (blkPl_297).base + 164#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 →
    s.trace = s0.trace → s.readReg64 (Reg.gpr 21#5) = x.slot →
    s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (polyEncoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) :=
  PolyEncoderBudget.polyEncoder_loop_le_exit_cro hFromCall

/-- Code-loaded placed budget loop key-decoding step at `+0x0a4` (`(blkPl_297).base + 164#64`)
when `¬ cur.length ≤ limit`. -/
theorem polyEncoder_decode_key_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {cur : List (BitVec 8)} {limit : Nat}
    {evs_acc : List AllocEvent} :
    ¬ cur.length ≤ limit → (s0.sp &&& 15#64 == 0#64) = true →
    cur.length ≤ x.bs.length → cur.length < 2 ^ 63 → IsDropSuffix x.bs cur →
    PolyMergeLoopEnv (2 * (x.bs.length - cur.length)) x.bs.length
      (polyEncoderCapBound x) evs_acc →
    st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur
      (PolyMergeLoopEnv (2 * cur.length + 2) x.bs.length (polyEncoderCapBound x)) →
    (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin PolynomialEncoder.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
    (∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_297).base + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_297).base + 164#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (polyEncoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) :=
  PolyEncoderBudget.polyEncoder_decode_key_step_cro hFromCall hVarintCall

/-- Code-loaded placed budget main loop induction for `PolynomialEncoder::merge` at `+0x0a4`
(`(blkPl_297).base + 164#64`). -/
theorem polyEncoder_loop_ok_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 : M.σ} {R : SepProp} {s0 : State} {limit : Nat} :
    FitsEnv M lim st0 (PolyEncoderMergeEnv x) →
    (s0.sp &&& 15#64 == 0#64) = true → limit < 2 ^ 63 →
    ∀ (n : Nat) (m : PolynomialEncoder) (cur : List (BitVec 8)) (st_cur : M.σ)
        (evs_acc : List AllocEvent) (s : State),
      cur.length ≤ n →
      cur.length ≤ x.bs.length →
      m.pts.length + cur.length < 2 ^ 56 →
      m.polys.length + cur.length < 2 ^ 56 →
      m.pts.length + cur.length ≤ polyEncoderCapBound x →
      m.polys.length + cur.length ≤ polyEncoderCapBound x →
      IsDropSuffix x.bs cur →
      PolyMergeLoopEnv (2 * (x.bs.length - cur.length)) x.bs.length
        (polyEncoderCapBound x) evs_acc →
      st_cur = M.stepEvents evs_acc st0 →
      (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin PolynomialEncoder.mergeField (cur.length - limit) m cur limit 97).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_297).base + 164#64 →
      s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
        (polyEncoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) :=
  PolyEncoderBudget.polyEncoder_loop_ok_cro
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall

/-- `withLsCodeRoLoaded`-callee contract-parameterized `[LibsignalPlacement]` budget verification of
`prost::encoding::message::merge::<PolynomialEncoder, &mut &[u8]>` (Block `297`). -/
theorem polyEncoderMerge_cro_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (blkPl_297).base
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)) :=
  PolyEncoderBudget.polyEncoderMerge_cro_placed_ok_of_contracts
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall

/-! ## 2. Code-Loaded (`withLsCodeLoaded`) `[LibsignalPlacement]` Top-Level Wrapper -/

/-- Code-loaded (`withLsCodeLoaded` on `261/257/291/263` + `withLsCodeRoLoaded` on `290` +
`growOneVecU8BudgetSpec`) contract-parameterized `[LibsignalPlacement]` budget verification of
`PolynomialEncoder::merge` (Block `297`). -/
theorem polyEncoderMerge_cl_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (blkPl_297).base
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)) :=
  PolyEncoderBudget.polyEncoderMerge_cl_placed_ok_of_contracts
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlacedBudget
