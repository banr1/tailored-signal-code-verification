/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8bPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8b
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 8 (`EkReceivedCt1Sampled`, `+1764`, Block `333`) — Part B

Lifts the Variant 8 PB-to-stack copy (`+1764..+1872`), `s.uc = none` error exit (`FreeOnlyEvs`),
and `es`/`ct1`/`ek` byte-length validation (`+1872 -> +1936 -> +2100 | +1972`) to `VmPreserved`
and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8bPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt statesFromPbJumpTablePlacedAt
   statesFromPbSavedCells statesFromPbStack v1_optProtoPolyEncoderHeap
   v1_optProtoPolyEncoderWordsAt v8_memRegion_1392_split_896_128_368
   v8_merge_1392_128_1520 v8_merge_368_ucWords_496 v8_pb128At
   v8_pb128_entails_full_224 v8_ucWordsAt v8_ucWordsAt_entails_128)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status
   stripS_trace vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (FromPbAllocHooksBudget seq_clean_lscl_st v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlacedBudget
  (v8_drop_sendingCt1_4212_of_sub_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

@[local simp]
private theorem stripS_readVReg128 (keep : BitVec 64 → Bool) (s : State) (r : BitVec 5) :
    (ProofLib.stripS keep s).readVReg128 r = s.readVReg128 r :=
  rfl

/-! ## 1. PB-to-Stack Copy (`+1764..+1872`) and `s.uc = none` Error Path -/

/-- `VmPreserved`-strengthened copy of the 184-byte payload `pbA + 8..192` to
    `fsp + 1392..1576` (`+1764..+1872`), branching to `+4212` if `u8 + 1 == 0`
    (`u8 = noneCap`) or falling through to `+1872`. -/
theorem v8_copy_pb_to_stack_1764_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1764#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (if (u8 + 1#64 == 0#64) = true
       then lsmpl.base 333 + 4212#64
       else lsmpl.base 333 + 1872#64)
      s1
      (memRegion (s0.sp - 2400#64) 2304 ∗
        v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
          w0 w8 w16 w24 w32 w40 w48 ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          memRegion (s0.sp - 2400#64) 1392 ∗
          v8_ucWordsAt (s0.sp - 2400#64 + 1392#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64)
            w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
          v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
            w0 w8 w16 w24 w32 w40 w48 ∗
          Rest) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x23 = s1.readReg64 .x23 ∧
        s2.readReg64 .x26 = u8 ∧
        s2.readReg64 .x27 = pbA ∧
        TraceCalleeSaved s2 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant8bPlaced.v8_copy_pb_to_stack_1764_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
      w0 w8 w16 w24 w32 w40 w48 Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun s2 P2 hvm ⟨hP2, hsp2, hx19_2, hx23_2, hx26_2, hx27_2, htr2⟩ =>
      ⟨hP2, hvm, by simpa using hsp2, by simpa using hx19_2,
       by simpa using hx23_2, by simpa using hx26_2, by simpa using hx27_2,
       ⟨by simpa using htr2.1, by simpa using htr2.2⟩⟩

theorem v8_copy_pb_to_stack_1764_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1764#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (if (u8 + 1#64 == 0#64) = true
       then lsmpl.base 333 + 4212#64
       else lsmpl.base 333 + 1872#64)
      s1
      (memRegion (s0.sp - 2400#64) 2304 ∗
        v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
          w0 w8 w16 w24 w32 w40 w48 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          memRegion (s0.sp - 2400#64) 1392 ∗
          v8_ucWordsAt (s0.sp - 2400#64 + 1392#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64)
            w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
          v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
            w0 w8 w16 w24 w32 w40 w48 ∗
          A.pool lim st s2 ∗
          Rest) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x23 = s1.readReg64 .x23 ∧
        s2.readReg64 .x26 = u8 ∧
        s2.readReg64 .x27 = pbA ∧
        TraceCalleeSaved s2 s0) := by
  have hwp := v8_copy_pb_to_stack_1764_placed (ext := ext) s0 s1 out pbA
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    w0 w8 w16 w24 w32 w40 w48 (A.pool lim st s1 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  refine SepWP.mono hwp fun s2 P2 _ _ ⟨hP2, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP2
  exact ⟨Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- Generalized (`Rest`-parametric) Variant 8 error path when `s.uc = none`
    (`+1764 -> +4212 -> s0.x30`) from a Block-`271` `withLsCodeLoaded` contract. -/
theorem v8_ekReceivedCt1Sampled_uc_none_rest_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop_cl : subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1764#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 192#64) 32 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        Rest ∗
        A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            Rest ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hcopy := v8_copy_pb_to_stack_1764_placed_budget A lim st (ext := ext) s0 s1 out pbA
    noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    w0 w8 w16 w24 w32 w40 w48
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     (pbA ↦₆₄ 0x8000000000000008#64) ∗
     memRegion (pbA + 192#64) 32 ∗
     v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
     Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  have hcmn : (noneCap + 1#64 == 0#64) = true := by decide
  simp only [hcmn, ↓reduceIte] at hcopy
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 333 + 4212#64)
    (P_mid := fun s2 =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 1520 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      A.pool lim st s2 ∗
      (memRegion pbA optProtoInnerStateSize ∗ Rest))
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      TraceCalleeSaved s2 s0)
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono hcopy fun s2 P2 _ _ ⟨hP2, _, hsp2, hx19_2, _, _, _, htr2⟩ => ?_)) ?_
  · refine ⟨Entails.trans hP2 ?_, hsp2, hx19_2, htr2⟩
    have huc := v8_ucWordsAt_entails_128 (s0.sp - 2400#64 + 1392#64)
      noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    have h1520 := v8_merge_1392_128_1520 (s0.sp - 2400#64)
    have hpb := v8_pb128_entails_full_224 pbA
      noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
      w0 w8 w16 w24 w32 w40 w48
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 1392 ∗
       v8_ucWordsAt (s0.sp - 2400#64 + 1392#64)
         noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128) ∗
      ((pbA ↦₆₄ 0x8000000000000008#64) ∗
       v8_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
         w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 192#64) 32) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       A.pool lim st s2 ∗
       Rest) by sep_ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono (Entails.trans (sepConj_mono_right huc) h1520) (sepConj_mono_left hpb))
      (Entails.of_eq (by sep_ac_rfl))
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, htr2⟩
    have hdrop := v8_drop_sendingCt1_4212_of_sub_placed (F := F) hdrop_cl st s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48
      (memRegion pbA optProtoInnerStateSize ∗ Rest)
      hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 htr2
    refine SepWP.mono hdrop fun sf Pf _ _ ⟨evs, hevs, hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcc_f, htr_f⟩

/-- Generalized (`Rest`-parametric) Variant 8 `s.uc = none` error path from `HookSat` on
    `spqrRustDeallocSym`. -/
theorem v8_ekReceivedCt1Sampled_uc_none_rest_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1764#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 192#64) 32 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        Rest ∗
        A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            Rest ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v8_ekReceivedCt1Sampled_uc_none_rest_of_sub_placed
    (v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed hdealloc)
    st s0 s1 out pbA u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    optEnc w0 w8 w16 w24 w32 w40 w48 Rest
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

/-- Generalized (`Rest`-parametric) Variant 8 `s.uc = none` error path under
    `FromPbAllocHooksBudget`. -/
theorem v8_ekReceivedCt1Sampled_uc_none_rest_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1764#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 192#64) 32 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        Rest ∗
        A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            Rest ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v8_ekReceivedCt1Sampled_uc_none_rest_of_dealloc_placed hA.dealloc
    st s0 s1 out pbA u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    optEnc w0 w8 w16 w24 w32 w40 w48 Rest
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

/-- Variant 8 error path when `s.uc = none` (`+1764 -> +4212 -> s0.x30`) from a Block-`271`
    `withLsCodeLoaded` contract. -/
theorem v8_ekReceivedCt1Sampled_uc_none_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop_cl : subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1764#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 192#64) 32 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  v8_ekReceivedCt1Sampled_uc_none_rest_of_sub_placed hdrop_cl st s0 s1 out pbA
    u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    optEnc w0 w8 w16 w24 w32 w40 w48 statesFromPbJumpTablePlacedAt
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

/-- Variant 8 error path when `s.uc = none` (`+1764 -> +4212 -> s0.x30`) from `HookSat` on
    `spqrRustDeallocSym`. -/
theorem v8_ekReceivedCt1Sampled_uc_none_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1764#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 192#64) 32 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v8_ekReceivedCt1Sampled_uc_none_of_sub_placed
    (v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed hdealloc)
    st s0 s1 out pbA u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    optEnc w0 w8 w16 w24 w32 w40 w48
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

/-- Variant 8 error path when `s.uc = none` (`+1764 -> +4212 -> s0.x30`) under
    `FromPbAllocHooksBudget`. -/
theorem v8_ekReceivedCt1Sampled_uc_none_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1764#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 192#64) 32 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v8_ekReceivedCt1Sampled_uc_none_of_dealloc_placed hA.dealloc
    st s0 s1 out pbA u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    optEnc w0 w8 w16 w24 w32 w40 w48
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

/-! ## 2. Step 1 (`+1872 -> +1936`) and Length Check (`+1936 -> +2100 | +1972`) -/

/-- `VmPreserved`-strengthened steps `+1872 -> +1936` (`lsmpl.base 333 + 1872 -> +1936`), copying
    `u8..u32` and `u72..u128` to `fsp + 896..928` and `fsp + 960..1024`, and loading `x9 = u24`,
    `q0 = u48 ++ u40`, `q1 = u64 ++ u56`. -/
theorem v8_copy_uc_1872_to_1936_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (z896 z904 z912 z920 z960 z968 z976 z984 z992 z1000 z1008 z1016 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = s0.sp - 2400#64 + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1936#64) s1
      (v8_ucWordsAt (pbA + 8#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        ((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 896#64) ↦₆₄ z896) ∗
        ((s0.sp - 2400#64 + 904#64) ↦₆₄ z904) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ z912) ∗
        ((s0.sp - 2400#64 + 920#64) ↦₆₄ z920) ∗
        ((s0.sp - 2400#64 + 960#64) ↦₆₄ z960) ∗
        ((s0.sp - 2400#64 + 968#64) ↦₆₄ z968) ∗
        ((s0.sp - 2400#64 + 976#64) ↦₆₄ z976) ∗
        ((s0.sp - 2400#64 + 984#64) ↦₆₄ z984) ∗
        ((s0.sp - 2400#64 + 992#64) ↦₆₄ z992) ∗
        ((s0.sp - 2400#64 + 1000#64) ↦₆₄ z1000) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ z1008) ∗
        ((s0.sp - 2400#64 + 1016#64) ↦₆₄ z1016) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (pbA + 8#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          ((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
          ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
          ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗
          ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
          ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
          ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
          ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
          ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
          ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
          ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = u24 ∧
        sm.readVReg128 0#5 = u48 ++ u40 ∧
        sm.readVReg128 1#5 = u64 ++ u56 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant8bPlaced.v8_copy_uc_1872_to_1936_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
      z896 z904 z912 z920 z960 z968 z976 z984 z992 z1000 z1008 z1016 Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx23_1)
      (by simpa using hx26_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx9_m, hq0_m, hq1_m, hx19_m, hx26_m, hx27_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx9_m,
       by simpa using hq0_m, by simpa using hq1_m, by simpa using hx19_m,
       by simpa using hx26_m, by simpa using hx27_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v8_copy_uc_1872_to_1936_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (z896 z904 z912 z920 z960 z968 z976 z984 z992 z1000 z1008 z1016 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = s0.sp - 2400#64 + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1936#64) s1
      (v8_ucWordsAt (pbA + 8#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        ((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 896#64) ↦₆₄ z896) ∗
        ((s0.sp - 2400#64 + 904#64) ↦₆₄ z904) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ z912) ∗
        ((s0.sp - 2400#64 + 920#64) ↦₆₄ z920) ∗
        ((s0.sp - 2400#64 + 960#64) ↦₆₄ z960) ∗
        ((s0.sp - 2400#64 + 968#64) ↦₆₄ z968) ∗
        ((s0.sp - 2400#64 + 976#64) ↦₆₄ z976) ∗
        ((s0.sp - 2400#64 + 984#64) ↦₆₄ z984) ∗
        ((s0.sp - 2400#64 + 992#64) ↦₆₄ z992) ∗
        ((s0.sp - 2400#64 + 1000#64) ↦₆₄ z1000) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ z1008) ∗
        ((s0.sp - 2400#64 + 1016#64) ↦₆₄ z1016) ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (pbA + 8#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          ((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
          ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
          ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗
          ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
          ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
          ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
          ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
          ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
          ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
          ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
          A.pool lim st sm ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = u24 ∧
        sm.readVReg128 0#5 = u48 ++ u40 ∧
        sm.readVReg128 1#5 = u64 ++ u56 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v8_copy_uc_1872_to_1936_placed (ext := ext) s0 s1 out pbA
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    z896 z904 z912 z920 z960 z968 z976 z984 z992 z1000 z1008 z1016
    (A.pool lim st s1 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened length-error branch at `+1936` (`+1936 -> +2100`) when
    `u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64`. -/
theorem v8_check_lengths_1936_err_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (z928 z936 z944 z952 : BitVec 64)
    (Rest : SepProp)
    (herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = u24)
    (hq0_1 : s1.readVReg128 0#5 = u48 ++ u40)
    (hq1_1 : s1.readVReg128 1#5 = u64 ++ u56)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2100#64) s1
      (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
        ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
        ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
        ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
        ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗
        ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
        ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
        ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant8bPlaced.v8_check_lengths_1936_err_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
      z928 z936 z944 z952 Rest herr hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx9_1) (by simpa using hq0_1) (by simpa using hq1_1)
      (by simpa using hx19_1) ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx19_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v8_check_lengths_1936_err_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (z928 z936 z944 z952 : BitVec 64)
    (Rest : SepProp)
    (herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = u24)
    (hq0_1 : s1.readVReg128 0#5 = u48 ++ u40)
    (hq1_1 : s1.readVReg128 1#5 = u64 ++ u56)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2100#64) s1
      (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
        ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
        ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
        ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
        ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗
        ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
        ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
        ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          A.pool lim st sm ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v8_check_lengths_1936_err_placed (ext := ext) s0 s1 out
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    z928 z936 z944 z952 (A.pool lim st s1 ∗ Rest)
    herr hsp0_align hpc1 hrun1 hsp1 hx9_1 hq0_1 hq1_1 hx19_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

private theorem v8_check_lengths_1936_err_x26_placed_raw [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (z928 z936 z944 z952 : BitVec 64)
    (Rest : SepProp)
    (herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = u24)
    (hq0_1 : s1.readVReg128 0#5 = u48 ++ u40)
    (hq1_1 : s1.readVReg128 1#5 = u64 ++ u56)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2100#64) s1
      (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
        ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
        ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
        ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
        ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗
        ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
        ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
        ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = s1.readReg64 .x26 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  change s1.pc = (blkPl_333).base + 1936#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 2100#64) s1 _ _
  by_cases h24 : u24 = 2080#64
  · subst h24
    by_cases h72 : u72 = 960#64
    · subst h72
      have h48 : u48 ≠ 1152#64 := by
        rcases herr with h | h | h
        · exact False.elim (h rfl)
        · exact False.elim (h rfl)
        · exact h
      have h48_bne : (u48 != 1152#64) = true := bne_iff_ne.mpr h48
      wp_steps; simp only [v8_ucWordsAt, sepConj_assoc]; wp_done
    · have h72_bne : (u72 != 960#64) = true := bne_iff_ne.mpr h72
      wp_steps; simp only [v8_ucWordsAt, sepConj_assoc]; wp_done
  · have h24_bne : (u24 != 2080#64) = true := bne_iff_ne.mpr h24
    wp_steps; simp only [v8_ucWordsAt, sepConj_assoc]; wp_done

/-- `x26`- and `VmPreserved`-preserving length-error branch at `+1936` (`+1936 -> +2100`). -/
theorem v8_check_lengths_1936_err_x26_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (z928 z936 z944 z952 : BitVec 64)
    (Rest : SepProp)
    (herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = u24)
    (hq0_1 : s1.readVReg128 0#5 = u48 ++ u40)
    (hq1_1 : s1.readVReg128 1#5 = u64 ++ u56)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2100#64) s1
      (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
        ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
        ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
        ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
        ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗
        ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
        ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
        ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = s1.readReg64 .x26 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (v8_check_lengths_1936_err_x26_placed_raw
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
      z928 z936 z944 z952 Rest herr hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx9_1) (by simpa using hq0_1) (by simpa using hq1_1)
      (by simpa using hx19_1) ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx26_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx19_m, by simpa using hx26_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v8_check_lengths_1936_err_x26_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (z928 z936 z944 z952 : BitVec 64)
    (Rest : SepProp)
    (herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = u24)
    (hq0_1 : s1.readVReg128 0#5 = u48 ++ u40)
    (hq1_1 : s1.readVReg128 1#5 = u64 ++ u56)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2100#64) s1
      (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
        ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
        ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
        ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
        ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗
        ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
        ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
        ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          A.pool lim st sm ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = s1.readReg64 .x26 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v8_check_lengths_1936_err_x26_placed (ext := ext) s0 s1 out
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    z928 z936 z944 z952 (A.pool lim st s1 ∗ Rest)
    herr hsp0_align hpc1 hrun1 hsp1 hx9_1 hq0_1 hq1_1 hx19_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened length-ok fallthrough at `+1936` (`+1936 -> +1972`) when
    `u24 = 2080#64 ∧ u72 = 960#64 ∧ u48 = 1152#64`. -/
theorem v8_check_lengths_1936_ok_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (z928 z936 z944 z952 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = 2080#64)
    (hq0_1 : s1.readVReg128 0#5 = 1152#64 ++ u40)
    (hq1_1 : s1.readVReg128 1#5 = u64 ++ u56)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1972#64) s1
      (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗
        ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
        ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
        ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
        ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
        ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗
        ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
        ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
        ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = s1.readReg64 .x26 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant8bPlaced.v8_check_lengths_1936_ok_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 u128
      z928 z936 z944 z952 Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx9_1) (by simpa using hq0_1) (by simpa using hq1_1)
      (by simpa using hx19_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx26_m, hx27_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx19_m,
       by simpa using hx26_m, by simpa using hx27_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v8_check_lengths_1936_ok_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (z928 z936 z944 z952 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = 2080#64)
    (hq0_1 : s1.readVReg128 0#5 = 1152#64 ++ u40)
    (hq1_1 : s1.readVReg128 1#5 = u64 ++ u56)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1972#64) s1
      (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗
        ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
        ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
        ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
        ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
        ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗
        ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
        ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
        ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
          A.pool lim st sm ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = s1.readReg64 .x26 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v8_check_lengths_1936_ok_placed (ext := ext) s0 s1 out pbA
    u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 u128
    z928 z936 z944 z952 (A.pool lim st s1 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx9_1 hq0_1 hq1_1 hx19_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened combined step `+1872 -> +2100` when
    `u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64`. -/
theorem v8_step_1872_to_2100_len_err_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp)
    (herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = s0.sp - 2400#64 + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2100#64) s1
      (memRegion (s0.sp - 2400#64) 1392 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        v8_ucWordsAt (pbA + 8#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (s0.sp - 2400#64) 896 ∗
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
          v8_ucWordsAt (pbA + 8#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant8bPlaced.v8_step_1872_to_2100_len_err_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
      Rest herr hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx23_1)
      (by simpa using hx26_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx19_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v8_step_1872_to_2100_len_err_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp)
    (herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = s0.sp - 2400#64 + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2100#64) s1
      (memRegion (s0.sp - 2400#64) 1392 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        v8_ucWordsAt (pbA + 8#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (s0.sp - 2400#64) 896 ∗
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
          v8_ucWordsAt (pbA + 8#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          A.pool lim st sm ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v8_step_1872_to_2100_len_err_placed (ext := ext) s0 s1 out pbA
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    (A.pool lim st s1 ∗ Rest) herr hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `x26`- and `VmPreserved`-preserving combined step `+1872 -> +2100` when
    `u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64`. -/
theorem v8_step_1872_to_2100_len_err_x26_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp)
    (herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = s0.sp - 2400#64 + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2100#64) s1
      (memRegion (s0.sp - 2400#64) 1392 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        v8_ucWordsAt (pbA + 8#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (s0.sp - 2400#64) 896 ∗
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
          v8_ucWordsAt (pbA + 8#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = u8 ∧
        TraceCalleeSaved sm s0) := by
  refine SepWP.weaken_pre
    (sepConj_mono_left (v8_memRegion_1392_split_896_128_368 (s0.sp - 2400#64))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro z1016
  apply ProofLib.SepWP.exists_left; intro z1008
  apply ProofLib.SepWP.exists_left; intro z1000
  apply ProofLib.SepWP.exists_left; intro z992
  apply ProofLib.SepWP.exists_left; intro z984
  apply ProofLib.SepWP.exists_left; intro z976
  apply ProofLib.SepWP.exists_left; intro z968
  apply ProofLib.SepWP.exists_left; intro z960
  apply ProofLib.SepWP.exists_left; intro z952
  apply ProofLib.SepWP.exists_left; intro z944
  apply ProofLib.SepWP.exists_left; intro z936
  apply ProofLib.SepWP.exists_left; intro z928
  apply ProofLib.SepWP.exists_left; intro z920
  apply ProofLib.SepWP.exists_left; intro z912
  apply ProofLib.SepWP.exists_left; intro z904
  apply ProofLib.SepWP.exists_left; intro z896
  have hcopy := v8_copy_uc_1872_to_1936_placed (ext := ext) s0 s1 out pbA
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    z896 z904 z912 z920 z960 z968 z976 z984 z992 z1000 z1008 z1016
    (memRegion (s0.sp - 2400#64) 896 ∗
      ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
      ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
      ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
      ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
      memRegion (s0.sp - 2400#64 + 1024#64) 368 ∗
      ((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗
      ((s0.sp - 2400#64 + 1392#64 + 16#64) ↦₆₄ u24) ∗
      ((s0.sp - 2400#64 + 1392#64 + 24#64) ↦₆₄ u32) ∗
      ((s0.sp - 2400#64 + 1392#64 + 32#64) ↦₆₄ u40) ∗
      ((s0.sp - 2400#64 + 1392#64 + 40#64) ↦₆₄ u48) ∗
      ((s0.sp - 2400#64 + 1392#64 + 48#64) ↦₆₄ u56) ∗
      ((s0.sp - 2400#64 + 1392#64 + 56#64) ↦₆₄ u64) ∗
      ((s0.sp - 2400#64 + 1392#64 + 64#64) ↦₆₄ u72) ∗
      ((s0.sp - 2400#64 + 1392#64 + 72#64) ↦₆₄ u80) ∗
      ((s0.sp - 2400#64 + 1392#64 + 80#64) ↦₆₄ u88) ∗
      ((s0.sp - 2400#64 + 1392#64 + 88#64) ↦₆₄ u96) ∗
      ((s0.sp - 2400#64 + 1392#64 + 96#64) ↦₆₄ u104) ∗
      ((s0.sp - 2400#64 + 1392#64 + 104#64) ↦₆₄ u112) ∗
      ((s0.sp - 2400#64 + 1392#64 + 112#64) ↦₆₄ u120) ∗
      ((s0.sp - 2400#64 + 1392#64 + 120#64) ↦₆₄ u128) ∗
      Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 hx27_1 htr1
  have h1400 : (s0.sp - 2400#64 + 1392#64) + 8#64 = s0.sp - 2400#64 + 1400#64 := by bv_omega
  refine SepWP.seq
    (SepWP.weaken_pre
      (by dsimp only [v8_ucWordsAt]; rw [h1400]; exact Entails.of_eq (by sep_ac_rfl))
      hcopy) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hvm1, hsp2, hx9_2, hq0_2, hq1_2, hx19_2, hx26_2, _, htr2⟩
  have hm496 := v8_merge_368_ucWords_496 (s0.sp - 2400#64)
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
  have hP2' : P2 ⊢
      ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
      ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
      ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗
      ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
      ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
      ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
      ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
      ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
      ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗
      ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
      ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
      ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
      ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
      ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
      ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
      ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
      (memRegion (s0.sp - 2400#64) 896 ∗
       memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
       v8_ucWordsAt (pbA + 8#64)
         u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
       Rest) := by
    refine Entails.trans hP2 ?_
    dsimp only [v8_ucWordsAt] at hm496 ⊢
    rw [h1400] at hm496
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64 + 1024#64) 368 ∗
       (((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 1392#64 + 16#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 1392#64 + 24#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 1392#64 + 32#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 1392#64 + 40#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 1392#64 + 48#64) ↦₆₄ u56) ∗
        ((s0.sp - 2400#64 + 1392#64 + 56#64) ↦₆₄ u64) ∗
        ((s0.sp - 2400#64 + 1392#64 + 64#64) ↦₆₄ u72) ∗
        ((s0.sp - 2400#64 + 1392#64 + 72#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 1392#64 + 80#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 1392#64 + 88#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 1392#64 + 96#64) ↦₆₄ u104) ∗
        ((s0.sp - 2400#64 + 1392#64 + 104#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1392#64 + 112#64) ↦₆₄ u120) ∗
        ((s0.sp - 2400#64 + 1392#64 + 120#64) ↦₆₄ u128))) ∗
      (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗
       ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
       ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗
       ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
       ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗
       ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
       ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗
       ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗
       ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗
       ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
       ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
       ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗
       ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗
       ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
       ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗
       ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗
       memRegion (s0.sp - 2400#64) 896 ∗
       ((pbA + 8#64) ↦₆₄ u8) ∗
       ((pbA + 8#64 + 8#64) ↦₆₄ u16) ∗
       ((pbA + 8#64 + 16#64) ↦₆₄ u24) ∗
       ((pbA + 8#64 + 24#64) ↦₆₄ u32) ∗
       ((pbA + 8#64 + 32#64) ↦₆₄ u40) ∗
       ((pbA + 8#64 + 40#64) ↦₆₄ u48) ∗
       ((pbA + 8#64 + 48#64) ↦₆₄ u56) ∗
       ((pbA + 8#64 + 56#64) ↦₆₄ u64) ∗
       ((pbA + 8#64 + 64#64) ↦₆₄ u72) ∗
       ((pbA + 8#64 + 72#64) ↦₆₄ u80) ∗
       ((pbA + 8#64 + 80#64) ↦₆₄ u88) ∗
       ((pbA + 8#64 + 88#64) ↦₆₄ u96) ∗
       ((pbA + 8#64 + 96#64) ↦₆₄ u104) ∗
       ((pbA + 8#64 + 104#64) ↦₆₄ u112) ∗
       ((pbA + 8#64 + 112#64) ↦₆₄ u120) ∗
       ((pbA + 8#64 + 120#64) ↦₆₄ u128) ∗
       Rest) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hm496) (Entails.of_eq (by sep_ac_rfl))
  have hchk := v8_check_lengths_1936_err_x26_placed (ext := ext) s0 s2 out
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    z928 z936 z944 z952
    (memRegion (s0.sp - 2400#64) 896 ∗
     memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
     v8_ucWordsAt (pbA + 8#64)
       u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
     Rest)
    herr hsp0_align hpc2 hrun2 hsp2 hx9_2 hq0_2 hq1_2 hx19_2 htr2
  refine SepWP.weaken_pre hP2' (SepWP.mono hchk fun sf Pf _ _ ⟨hPf, hvm2, hsp_f, hx19_f, hx26_f, htr_f⟩ => ?_)
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hvm1.trans hvm2,
    hsp_f, hx19_f, hx26_f.trans hx26_2, htr_f⟩

theorem v8_step_1872_to_2100_len_err_x26_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp)
    (herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = s0.sp - 2400#64 + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2100#64) s1
      (memRegion (s0.sp - 2400#64) 1392 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        v8_ucWordsAt (pbA + 8#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (s0.sp - 2400#64) 896 ∗
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
          v8_ucWordsAt (pbA + 8#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          A.pool lim st sm ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = u8 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v8_step_1872_to_2100_len_err_x26_placed (ext := ext) s0 s1 out pbA
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    (A.pool lim st s1 ∗ Rest) herr hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8bPlacedBudget
