/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 5d `withLsCodeLoaded`: Arm 7 Call Steps

Relocatable `[LibsignalPlacement]` call step lemmas (`+2100 -> +2116` and `+2116 -> +2128` in
Block `334`) for Arm 7 (`States.ct1Sampled`) under `RustCliAllocBudget M`, with `withLsCodeLoaded`
on `<PolyEncoder>::into_pb` (Block `375`) and `<PolyDecoder>::into_pb` (Block `377`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dClPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement libsignalSessionCode lsmpl
   withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (PolyDecoder PolyEncoder)
open CryptoVerification.SpqrV1.Drop
  (none2Cap_add_two_beq_zero noneCap_add_two_beq_zero)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderAt polyDecoderSize polyEncoderAt polyEncoderSize
   protoPolynomialDecoderSize protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (TraceCalleeSaved bv_add_add_lit' bv_sub_sub_lit'
   protoPolynomialDecoderHeap protoPolynomialEncoderHeap)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv
   RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
  (DecoderIntoPbAllocEnv DecoderIntoPbEnv decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (EncoderIntoPbAllocEnv EncoderIntoPbEnv encoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlacedBudget
  (call_decoderIntoPb_expose_wp_cl_placed call_encoderIntoPb_expose_wp_cl_placed)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

export CryptoVerification.SpqrV1.States.IntoPb
  (polyEncoderTag polyEncoderTag_eq_zero_or_one)
export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux
  (Ct1CloneAllocEnv Ct1CloneAndDropEnv Ct1SampledEnv ct1SampledEnv_of_parts)

private theorem allocCallPreserved_trans {s0 s1 s2 : State}
    (h1 : AllocCallPreserved s0 s1) (h2 : AllocCallPreserved s1 s2) :
    AllocCallPreserved s0 s2 := by
  rcases h1 with ⟨hfs1, htr1, hsig1, htp1, hbs1, hor1, hsym1⟩
  rcases h2 with ⟨hfs2, htr2, hsig2, htp2, hbs2, hor2, hsym2⟩
  exact ⟨hfs2.trans hfs1, htr2.trans htr1, hsig2.trans hsig1,
    htp2.trans htp1, hbs2.trans hbs1, hor2.trans hor1, hsym2.trans hsym1⟩

private theorem sepWP_seq_lscl [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State} {P : SepProp}
    {post1 post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → post1 sm Pm →
      SepWP prog target sm Pm post) :
    SepWP prog target s P post :=
  SepWP.seq_frozen (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl
    (SepWP.mono h1 fun sm Pm hpcm hrunm hp1 hclm => h2 sm Pm hpcm hrunm hclm hp1)

/-! ## 1. Step 4 (`+2100 -> +2116` in Block `334`) with `withLsCodeLoaded` on `<PolyEncoder>::into_pb` -/

/-- Step 4 (`+2100 -> +2116` in Block `334`, direct `SepWP` form) with `withLsCodeLoaded` on
    `<PolyEncoder>::into_pb` (`lsmpl.base 375`) under `FitsEnv M lim st (EncoderIntoPbAllocEnv enc)`. -/
theorem ct1Sampled_step_2100_to_2116_wp_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (s0 s : State) (st : M.σ) (out stA ptr_new len_ct1 epoch : BitVec 64)
    (enc : PolyEncoder)
    (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfits : FitsEnv M lim st (EncoderIntoPbAllocEnv enc))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 2100#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = ptr_new)
    (hx22 : s.readReg64 .x22 = len_ct1)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 2116#64) s
      (memRegion (s0.sp - 1232#64) 56 ∗
       polyEncoderAt A.repAlloc stA enc ∗
       A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
      (fun sm Pm =>
        ∃ (evs : List AllocEvent) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
          EncoderIntoPbEnv enc evs ∧
          AllocCallPreserved s sm ∧
          (Pm ⊢
            (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
             ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
             ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
             ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
            protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
            memRegion stA polyEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame) ∧
          sm.sp = s0.sp - 1520#64 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = stA ∧
          sm.readReg64 .x21 = ptr_new ∧
          sm.readReg64 .x22 = len_ct1 ∧
          sm.readReg64 .x23 = s0.sp - 1360#64 ∧
          sm.readReg64 .x27 = s0.sp - 1360#64 ∧
          sm.readReg64 .x28 = epoch ∧
          TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsetup :
      SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
        (lsmpl.base 375) s
        (memRegion (s0.sp - 1232#64) 56 ∗
         polyEncoderAt A.repAlloc stA enc ∗
         A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
        (fun sc Pm =>
          VmPreserved s sc ∧
          (Pm ⊢
            memRegion (s0.sp - 1232#64) 56 ∗
            polyEncoderAt A.repAlloc stA enc ∗
            A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame) ∧
          AllocCallPreserved s sc ∧
          sc.sp = s0.sp - 1520#64 ∧
          sc.readReg64 .x29 = s0.sp - 96#64 ∧
          sc.readReg64 .x19 = out ∧
          sc.readReg64 .x20 = stA ∧
          sc.readReg64 .x21 = ptr_new ∧
          sc.readReg64 .x22 = len_ct1 ∧
          sc.readReg64 .x23 = s0.sp - 1360#64 ∧
          sc.readReg64 .x27 = s0.sp - 1360#64 ∧
          sc.readReg64 .x28 = epoch ∧
          sc.readReg64 .x0 = s0.sp - 1232#64 ∧
          sc.readReg64 .x1 = stA ∧
          sc.readReg64 .x30 = (blkPl_334).base + 2116#64 ∧
          TraceCalleeSaved sc s0) := by
    by_vm_steps (
      wp_steps
      wp_done)
  refine sepWP_seq_lscl hcl hsetup fun sc _Pm hpcc hrunc hclc
      ⟨hvmc, hPmc, hacp_sc, hspc, hx29c, hx19c, hx20c, hx21c, hx22c,
       hx23c, hx27c, hx28c, hx0c, hx1c, hx30c, htrc⟩ => ?_
  refine SepWP.weaken_pre hPmc ?_
  rw [← A.pool_of_vmPreserved hvmc]
  exact call_encoderIntoPb_expose_wp_cl_placed henc_cl st (s0.sp - 1232#64) stA enc
    hclc hpcc hrunc hspc hfsp_align hx30c htrc hx0c hx1c hfits
    (by dsimp only [protoPolynomialEncoderSize]; sep_ac_rfl)
    (fun sm evs e0 e1 e2 e3 e4 e5 e6 hpcm hrunm hspm hcc hacp_cm htrm henv =>
      SepWP.done hpcm hrunm
        ⟨evs, e0, e1, e2, e3, e4, e5, e6, henv, allocCallPreserved_trans hacp_sc hacp_cm,
          Entails.of_eq (by simp only [arm64_norm]),
          hspm,
          hcc.2.2.2.2.2.2.2.2.2.2.1.trans hx29c,
          hcc.1.trans hx19c,
          hcc.2.1.trans hx20c,
          hcc.2.2.1.trans hx21c,
          hcc.2.2.2.1.trans hx22c,
          hcc.2.2.2.2.1.trans hx23c,
          hcc.2.2.2.2.2.2.2.2.1.trans hx27c,
          hcc.2.2.2.2.2.2.2.2.2.1.trans hx28c,
          htrm⟩)

/-- Step 4 (`+2100 -> +2116` in Block `334`, CPS `SepWPp` form, parametric in `{Q Qp}`)
    with `withLsCodeLoaded` on `<PolyEncoder>::into_pb` (`lsmpl.base 375`), threading
    `LibsignalCodeLoaded lsmpl sm.mem` to `hnext`. -/
theorem ct1Sampled_step_2100_to_2116_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {Q Qp : State → SepProp → Prop}
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (s0 s : State) (st : M.σ) (out stA ptr_new len_ct1 epoch : BitVec 64)
    (enc : PolyEncoder)
    (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfits : FitsEnv M lim st (EncoderIntoPbAllocEnv enc))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 2100#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = ptr_new)
    (hx22 : s.readReg64 .x22 = len_ct1)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (evs : List AllocEvent) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
      EncoderIntoPbEnv enc evs →
      AllocCallPreserved s sm →
      sm.pc = (blkPl_334).base + 2116#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = out →
      sm.readReg64 .x20 = stA →
      sm.readReg64 .x21 = ptr_new →
      sm.readReg64 .x22 = len_ct1 →
      sm.readReg64 .x23 = s0.sp - 1360#64 →
      sm.readReg64 .x27 = s0.sp - 1360#64 →
      sm.readReg64 .x28 = epoch →
      TraceCalleeSaved sm s0 →
      LibsignalCodeLoaded lsmpl sm.mem →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sm
        ((((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
          ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
          ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
          ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
         protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
         memRegion stA polyEncoderSize ∗
         A.pool lim (M.stepEvents evs st) sm ∗
         stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion (s0.sp - 1232#64) 56 ∗
       polyEncoderAt A.repAlloc stA enc ∗
       A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
      Q Qp := by
  have hwp := ct1Sampled_step_2100_to_2116_wp_cl_placed henc_cl s0 s st out stA
    ptr_new len_ct1 epoch enc Frame hcl hfits hsp0_align hpc hrun hsp hx29 hx19 hx20
    hx21 hx22 hx27 hx28 htrace
  refine SepWPp.seq_frozen (mid := (blkPl_334).base + 2116#64)
    (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl ?_
  refine SepWP.mono hwp fun sm Pm hpcm hrunm
      ⟨evs, e0, e1, e2, e3, e4, e5, e6, henv, hacp, hPm, hspm, hx29m, hx19m, hx20m,
        hx21m, hx22m, hx23m, hx27m, hx28m, htrm⟩ hclm =>
    SepWPp.weaken_pre hPm
      (hnext sm evs e0 e1 e2 e3 e4 e5 e6 henv hacp hpcm hrunm hspm hx29m hx19m hx20m
        hx21m hx22m hx23m hx27m hx28m htrm hclm)

/-! ## 2. Step 5 (`+2116 -> +2128` in Block `334`) with `withLsCodeLoaded` on `<PolyDecoder>::into_pb` -/

/-- Step 5 (`+2116 -> +2128` in Block `334`, direct `SepWP` form) with `withLsCodeLoaded` on
    `<PolyDecoder>::into_pb` (`lsmpl.base 377`) under `FitsEnv M lim st (DecoderIntoPbAllocEnv dec)`. -/
theorem ct1Sampled_step_2116_to_2128_wp_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (s0 s : State) (st : M.σ) (out stA ptr_new len_ct1 epoch : BitVec 64)
    (dec : PolyDecoder)
    (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfits : FitsEnv M lim st (DecoderIntoPbAllocEnv dec))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 2116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = ptr_new)
    (hx22 : s.readReg64 .x22 = len_ct1)
    (hx23 : s.readReg64 .x23 = s0.sp - 1360#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 2128#64) s
      (memRegion (s0.sp - 1176#64) 40 ∗
       polyDecoderAt A.repAlloc (stA + 528#64) dec ∗
       A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
      (fun sm Pm =>
        ∃ (evs : List AllocEvent) (d0 d1 d2 d3 d4 : BitVec 64),
          DecoderIntoPbEnv dec evs ∧
          AllocCallPreserved s sm ∧
          (Pm ⊢
            (((s0.sp - 1176#64) ↦₆₄ d0) ∗ ((s0.sp - 1168#64) ↦₆₄ d1) ∗
             ((s0.sp - 1160#64) ↦₆₄ d2) ∗ ((s0.sp - 1152#64) ↦₆₄ d3) ∗
             ((s0.sp - 1144#64) ↦₆₄ d4)) ∗
            protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 dec.intoPb ∗
            memRegion (stA + 528#64) polyDecoderSize ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame) ∧
          sm.sp = s0.sp - 1520#64 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x21 = ptr_new ∧
          sm.readReg64 .x22 = len_ct1 ∧
          sm.readReg64 .x27 = s0.sp - 1360#64 ∧
          sm.readReg64 .x28 = epoch ∧
          TraceCalleeSaved sm s0) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsetup :
      SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
        (lsmpl.base 377) s
        (memRegion (s0.sp - 1176#64) 40 ∗
         polyDecoderAt A.repAlloc (stA + 528#64) dec ∗
         A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
        (fun sc Pm =>
          VmPreserved s sc ∧
          (Pm ⊢
            memRegion (s0.sp - 1176#64) 40 ∗
            polyDecoderAt A.repAlloc (stA + 528#64) dec ∗
            A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame) ∧
          AllocCallPreserved s sc ∧
          sc.sp = s0.sp - 1520#64 ∧
          sc.readReg64 .x29 = s0.sp - 96#64 ∧
          sc.readReg64 .x19 = out ∧
          sc.readReg64 .x21 = ptr_new ∧
          sc.readReg64 .x22 = len_ct1 ∧
          sc.readReg64 .x27 = s0.sp - 1360#64 ∧
          sc.readReg64 .x28 = epoch ∧
          sc.readReg64 .x0 = s0.sp - 1176#64 ∧
          sc.readReg64 .x1 = stA + 528#64 ∧
          sc.readReg64 .x30 = (blkPl_334).base + 2128#64 ∧
          TraceCalleeSaved sc s0) := by
    by_vm_steps (
      wp_steps
      wp_done)
  refine sepWP_seq_lscl hcl hsetup fun sc _Pm hpcc hrunc hclc
      ⟨hvmc, hPmc, hacp_sc, hspc, hx29c, hx19c, hx21c, hx22c,
       hx27c, hx28c, hx0c, hx1c, hx30c, htrc⟩ => ?_
  refine SepWP.weaken_pre hPmc ?_
  rw [← A.pool_of_vmPreserved hvmc]
  exact call_decoderIntoPb_expose_wp_cl_placed hdec_cl st (s0.sp - 1176#64) (stA + 528#64) dec
    hclc hpcc hrunc hspc hfsp_align hx30c htrc hx0c hx1c hfits
    (by dsimp only [protoPolynomialDecoderSize]; sep_ac_rfl)
    (fun sm evs d0 d1 d2 d3 d4 hpcm hrunm hspm hcc hacp_cm htrm henv =>
      SepWP.done hpcm hrunm
        ⟨evs, d0, d1, d2, d3, d4, henv, allocCallPreserved_trans hacp_sc hacp_cm,
          Entails.of_eq (by simp only [arm64_norm]),
          hspm,
          hcc.2.2.2.2.2.2.2.2.2.2.1.trans hx29c,
          hcc.1.trans hx19c,
          hcc.2.2.1.trans hx21c,
          hcc.2.2.2.1.trans hx22c,
          hcc.2.2.2.2.2.2.2.2.1.trans hx27c,
          hcc.2.2.2.2.2.2.2.2.2.1.trans hx28c,
          htrm⟩)

/-- Step 5 (`+2116 -> +2128` in Block `334`, CPS `SepWPp` form, parametric in `{Q Qp}`)
    with `withLsCodeLoaded` on `<PolyDecoder>::into_pb` (`lsmpl.base 377`), threading
    `LibsignalCodeLoaded lsmpl sm.mem` to `hnext`. -/
theorem ct1Sampled_step_2116_to_2128_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {Q Qp : State → SepProp → Prop}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (s0 s : State) (st : M.σ) (out stA ptr_new len_ct1 epoch : BitVec 64)
    (dec : PolyDecoder)
    (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfits : FitsEnv M lim st (DecoderIntoPbAllocEnv dec))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 2116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = ptr_new)
    (hx22 : s.readReg64 .x22 = len_ct1)
    (hx23 : s.readReg64 .x23 = s0.sp - 1360#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (evs : List AllocEvent) (d0 d1 d2 d3 d4 : BitVec 64),
      DecoderIntoPbEnv dec evs →
      AllocCallPreserved s sm →
      sm.pc = (blkPl_334).base + 2128#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = out →
      sm.readReg64 .x21 = ptr_new →
      sm.readReg64 .x22 = len_ct1 →
      sm.readReg64 .x27 = s0.sp - 1360#64 →
      sm.readReg64 .x28 = epoch →
      TraceCalleeSaved sm s0 →
      LibsignalCodeLoaded lsmpl sm.mem →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sm
        ((((s0.sp - 1176#64) ↦₆₄ d0) ∗ ((s0.sp - 1168#64) ↦₆₄ d1) ∗
          ((s0.sp - 1160#64) ↦₆₄ d2) ∗ ((s0.sp - 1152#64) ↦₆₄ d3) ∗
          ((s0.sp - 1144#64) ↦₆₄ d4)) ∗
         protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 dec.intoPb ∗
         memRegion (stA + 528#64) polyDecoderSize ∗
         A.pool lim (M.stepEvents evs st) sm ∗
         stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion (s0.sp - 1176#64) 40 ∗
       polyDecoderAt A.repAlloc (stA + 528#64) dec ∗
       A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
      Q Qp := by
  have hwp := ct1Sampled_step_2116_to_2128_wp_cl_placed hdec_cl s0 s st out stA
    ptr_new len_ct1 epoch dec Frame hcl hfits hsp0_align hpc hrun hsp hx29 hx19 hx20
    hx21 hx22 hx23 hx27 hx28 htrace
  refine SepWPp.seq_frozen (mid := (blkPl_334).base + 2128#64)
    (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl ?_
  refine SepWP.mono hwp fun sm Pm hpcm hrunm
      ⟨evs, d0, d1, d2, d3, d4, henv, hacp, hPm, hspm, hx29m, hx19m,
        hx21m, hx22m, hx27m, hx28m, htrm⟩ hclm =>
    SepWPp.weaken_pre hPm
      (hnext sm evs d0 d1 d2 d3 d4 henv hacp hpcm hrunm hspm hx29m hx19m
        hx21m hx22m hx27m hx28m htrm hclm)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dClPlacedBudget
