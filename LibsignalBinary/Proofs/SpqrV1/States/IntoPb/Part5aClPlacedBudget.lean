/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 5a `withLsCodeLoaded`: Arm 8 (`States.ekReceivedCt1Sampled`)

Relocatable `[LibsignalPlacement]` verification of Arm 8 (`States.ekReceivedCt1Sampled`, tag `10`,
jump table index `8` -> `+1644`) under `RustCliAllocBudget M` and `EkReceivedCt1SampledEnv`,
taking `withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)` on `<PolyEncoder>::into_pb` (Block `375`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aClPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withLsCodeLoaded
   libsignalSessionCode lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (PolyEncoder States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (EkReceivedCt1Sampled)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly
  (polyEncoderAt polyEncoderSize protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (TraceCalleeSaved authenticatorHeap bv_add_add_lit' bv_sub_sub_lit'
   ekReceivedScratchCells epilogueStagingCells memRegion_1424_split_epilogue
   memRegion_ekReceived_scratch_split outWords28 protoPolynomialEncoderHeap
   stackAt_encoderIntoPb_eq_allocHook statesIntoPbJumpTablePlacedAt
   statesIntoPbSavedCells statesIntoPbSetLr statesIntoPbSetLr_lr
   statesIntoPbStack vecU8CloneTail vecU8Heap)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
   RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (EncoderIntoPbAllocEnv EncoderIntoPbEnv encoderIntoPbSpec encoderIntoPbVecs
   fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
  (sepWPp_of_states_into_pb_exit_cl_placed statesIntoPbVariantPlacedSpec
   statesIntoPbVariantPlacedSpecOfEnv states_into_pb_epilogue_placed
   states_into_pb_prologue_60_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlacedBudget
  (call_encoderIntoPb_expose_wp_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
  (StatesIntoPbAllocPlacedBudget)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlacedBudget
  (Ct1CloneAllocEnv Ct1CloneAndDropEnv EkReceivedCt1SampledEnv
   ekReceivedCt1SampledEnv_imp_spqrBoundedEvs ekReceivedCt1SampledEnv_of_parts
   ekReceivedCt1Sampled_step_1760_to_2252_wp_placed
   ekReceivedCt1Sampled_step_2252_to_2324_placed
   ekReceivedCt1Sampled_step_2340_to_1544_placed
   ekReceivedCt1Sampled_step_60_to_1760_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget
  (ct1CloneEvents ct1DeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux
  (chunkedEkReceivedCt1Sampled_expose ct1CloneAndDropEnv_of_dealloc
   ekReceivedScratchCells_entails_memRegions
   fitsEvents_clone_of_ct1CloneAndDropEnv
   outWords28_entails_ekReceivedCt1Sampled
   stA_ekReceivedCt1Sampled_entails_928)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

export CryptoVerification.SpqrV1.States.IntoPb
  (statesIntoPbSetLr statesIntoPbSetLr_lr)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlacedBudget
  (Ct1CloneAllocEnv Ct1CloneAndDropEnv EkReceivedCt1SampledEnv
   ekReceivedCt1SampledEnv_of_parts ekReceivedCt1SampledEnv_imp_spqrBoundedEvs)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-- Tight relocatable per-variant budget spec for `<States>::into_pb` on
    `.ekReceivedCt1Sampled s` over `EkReceivedCt1SampledEnv s`. -/
abbrev statesIntoPbEkReceivedCt1SampledPlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) :=
  statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ekReceivedCt1Sampled s)
    (EkReceivedCt1SampledEnv s)

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

/-! ## 1. Step 5 (`+2324 -> +2340` in Block `334`) with `withLsCodeLoaded` on `<PolyEncoder>::into_pb` -/

/-- Step 5 (`+2324 -> +2340` in Block `334`, direct `SepWP` form) with `withLsCodeLoaded` on
    `<PolyEncoder>::into_pb` (`lsmpl.base 375`) under `FitsEnv M lim st (EncoderIntoPbAllocEnv enc)`. -/
theorem ekReceivedCt1Sampled_step_2324_to_2340_wp_cl_placed [LibsignalPlacement]
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
    (hpc : s.pc = (blkPl_334).base + 2324#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 2340#64) s
      (memRegion (s0.sp - 1232#64) 56 ∗
       polyEncoderAt A.repAlloc (stA + 8#64) enc ∗
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
            memRegion (stA + 8#64) polyEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame) ∧
          sm.sp = s0.sp - 1520#64 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = stA ∧
          sm.readReg64 .x21 = len_ct1 ∧
          sm.readReg64 .x22 = ptr_new ∧
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
         polyEncoderAt A.repAlloc (stA + 8#64) enc ∗
         A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
        (fun sc Pm =>
          VmPreserved s sc ∧
          (Pm ⊢
            memRegion (s0.sp - 1232#64) 56 ∗
            polyEncoderAt A.repAlloc (stA + 8#64) enc ∗
            A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame) ∧
          AllocCallPreserved s sc ∧
          sc.sp = s0.sp - 1520#64 ∧
          sc.readReg64 .x29 = s0.sp - 96#64 ∧
          sc.readReg64 .x19 = out ∧
          sc.readReg64 .x20 = stA ∧
          sc.readReg64 .x21 = len_ct1 ∧
          sc.readReg64 .x22 = ptr_new ∧
          sc.readReg64 .x27 = s0.sp - 1360#64 ∧
          sc.readReg64 .x28 = epoch ∧
          sc.readReg64 .x0 = s0.sp - 1232#64 ∧
          sc.readReg64 .x1 = stA + 8#64 ∧
          sc.readReg64 .x30 = (blkPl_334).base + 2340#64 ∧
          TraceCalleeSaved sc s0) := by
    by_vm_steps (
      wp_steps
      wp_done)
  refine sepWP_seq_lscl hcl hsetup fun sc _Pm hpcc hrunc hclc
      ⟨hvmc, hPmc, hacp_sc, hspc, hx29c, hx19c, hx20c, hx21c, hx22c,
       hx27c, hx28c, hx0c, hx1c, hx30c, htrc⟩ => ?_
  refine SepWP.weaken_pre hPmc ?_
  rw [← A.pool_of_vmPreserved hvmc]
  exact call_encoderIntoPb_expose_wp_cl_placed henc_cl st (s0.sp - 1232#64) (stA + 8#64) enc
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
          hcc.2.2.2.2.2.2.2.2.1.trans hx27c,
          hcc.2.2.2.2.2.2.2.2.2.1.trans hx28c,
          htrm⟩)

/-- Step 5 (`+2324 -> +2340` in Block `334`, CPS `SepWPp` form, parametric in `{Q Qp}`)
    with `withLsCodeLoaded` on `<PolyEncoder>::into_pb` (`lsmpl.base 375`), threading
    `LibsignalCodeLoaded lsmpl sm.mem` to `hnext`. -/
theorem ekReceivedCt1Sampled_step_2324_to_2340_cl_placed [LibsignalPlacement]
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
    (hpc : s.pc = (blkPl_334).base + 2324#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = len_ct1)
    (hx22 : s.readReg64 .x22 = ptr_new)
    (hx27 : s.readReg64 .x27 = s0.sp - 1360#64)
    (hx28 : s.readReg64 .x28 = epoch)
    (htrace : TraceCalleeSaved s s0)
    (hnext : ∀ (sm : State) (evs : List AllocEvent) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
      EncoderIntoPbEnv enc evs →
      AllocCallPreserved s sm →
      sm.pc = (blkPl_334).base + 2340#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 1520#64 →
      sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = out →
      sm.readReg64 .x20 = stA →
      sm.readReg64 .x21 = len_ct1 →
      sm.readReg64 .x22 = ptr_new →
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
         memRegion (stA + 8#64) polyEncoderSize ∗
         A.pool lim (M.stepEvents evs st) sm ∗
         stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion (s0.sp - 1232#64) 56 ∗
       polyEncoderAt A.repAlloc (stA + 8#64) enc ∗
       A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame)
      Q Qp := by
  have hwp := ekReceivedCt1Sampled_step_2324_to_2340_wp_cl_placed henc_cl s0 s st out stA
    ptr_new len_ct1 epoch enc Frame hcl hfits hsp0_align hpc hrun hsp hx29 hx19 hx20
    hx21 hx22 hx27 hx28 htrace
  refine SepWPp.seq_frozen (mid := (blkPl_334).base + 2340#64)
    (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl ?_
  refine SepWP.mono hwp fun sm Pm hpcm hrunm
      ⟨evs, e0, e1, e2, e3, e4, e5, e6, henv, hacp, hPm, hspm, hx29m, hx19m, hx20m,
        hx21m, hx22m, hx27m, hx28m, htrm⟩ hclm =>
    SepWPp.weaken_pre hPm
      (hnext sm evs e0 e1 e2 e3 e4 e5 e6 henv hacp hpcm hrunm hspm hx29m hx19m hx20m
        hx21m hx22m hx27m hx28m htrm hclm)

/-! ## 2. Relocatable `withLsCodeLoaded` Main Theorems for Arm 8 (`States.ekReceivedCt1Sampled`) -/

/-- Envelope-parametric relocatable Arm 8 (`States.ekReceivedCt1Sampled`, tag `10`,
    jump table index `8` -> `+1644` in Block `334`) with `withLsCodeLoaded` on
    `<PolyEncoder>::into_pb` (`lsmpl.base 375`) and Block `334`. -/
theorem states_into_pb_ekReceivedCt1Sampled_of_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, EkReceivedCt1SampledEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ekReceivedCt1Sampled s) Env)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [statesIntoPbVariantPlacedSpecOfEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hfits_env⟩, hmem⟩
  have hfits : FitsEnv M lim st (EkReceivedCt1SampledEnv s) := FitsEnv.mono hEnv hfits_env
  have hfits_cd : FitsEnv M lim st (Ct1CloneAndDropEnv s.uc.ct1) := hfits.seq_left
  have hfits_clone : FitsEvents M lim st (ct1CloneEvents s.uc.ct1) :=
    fitsEvents_clone_of_ct1CloneAndDropEnv hfits_cd
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA (.ekReceivedCt1Sampled s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · dsimp only [statesIntoPbJumpTablePlacedAt,
      CryptoVerification.SpqrV1.Top.InitInner.statesIntoPbJumpTablePlacedAt] at hmem ⊢
    simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_exit_cl_placed st s0 s0 out stA
    (.ekReceivedCt1Sampled s) Env _ R ?_
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedEkReceivedCt1Sampled_expose A.repAlloc stA s))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro a0
  apply SepWP.exists_elim; intro a1
  apply SepWP.exists_elim; intro a2
  apply SepWP.exists_elim; intro a3
  apply SepWP.exists_elim; intro a4
  apply SepWP.exists_elim; intro a5
  apply SepWP.exists_elim; intro es0
  apply SepWP.exists_elim; intro es1
  apply SepWP.exists_elim; intro es2
  apply SepWP.exists_elim; intro ek0
  apply SepWP.exists_elim; intro ek1
  apply SepWP.exists_elim; intro ek2
  apply SepWP.exists_elim; intro cap_ct1
  apply SepWP.exists_elim; intro ptr_ct1
  rw [show memRegion out optProtoInnerStateSize ∗
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stA ↦₆₄ 10#64) ∗
      polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
      ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
      ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
      ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
      ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
      ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
      ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
      (ptr_ct1 ↦ₛ s.uc.ct1) ∗
      vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
      vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
      memRegion (stA + 536#64) 392 ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack =
      ⌜s.uc.ct1.length < 2 ^ 63⌝ ∗
      (stackAt s0.sp statesIntoPbStack ∗ (stA ↦₆₄ 10#64) ∗ A.pool lim st s0 ∗
       (statesIntoPbJumpTablePlacedAt ∗
        memRegion out optProtoInnerStateSize ∗
        polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
        ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
        ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
        ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
        ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
        ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
        ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
        (ptr_ct1 ↦ₛ s.uc.ct1) ∗
        vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
        authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
        vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
        memRegion (stA + 536#64) 392)) by sep_ac_rfl]
  apply SepWP.pure_elim; intro hlen
  have hpro := states_into_pb_prologue_60_placed (ext := ext) A lim st s0 out stA 10#64
    (statesIntoPbJumpTablePlacedAt ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc hrun hx8 hx0
  refine sepWP_seq_lscl hcl0 hpro fun s1 P1 hpc1 hrun1 hcl1 ⟨hP1, hsp1, hx29_1, hx28_1, hx27_1,
      hx26_1, hx20_1, hx19_1, hx8_1, htr1, _hvm1⟩ => ?_
  refine SepWP.weaken_pre hP1 ?_
  have h1424 :
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416 ⊢
      memRegion (s0.sp - 1520#64) 1424 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1520#64) (n := 8) (k := 1416)
          (b' := s0.sp - 1512#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (pointsTo64_entails_memRegion (s0.sp - 1520#64) 0#64)
  refine SepWP.weaken_pre
    (by
      rw [show stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗
          (stA ↦₆₄ 10#64) ∗ A.pool lim st s1 ∗
          (statesIntoPbJumpTablePlacedAt ∗
           memRegion out optProtoInnerStateSize ∗
           polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
           ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
           ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
           ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
           ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
           ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
           ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
           vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
           memRegion (stA + 536#64) 392) =
          (((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1512#64) 1416) ∗
          (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
           statesIntoPbSavedCells s0 ∗
           (stA ↦₆₄ 10#64) ∗
           statesIntoPbJumpTablePlacedAt ∗
           memRegion out optProtoInnerStateSize ∗
           polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
           ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
           ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
           ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
           ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
           ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
           ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
           (ptr_ct1 ↦ₛ s.uc.ct1) ∗
           vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
           vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
           memRegion (stA + 536#64) 392 ∗ A.pool lim st s1) by sep_ac_rfl]
      exact sepConj_mono_left (Entails.trans h1424 (memRegion_1424_split_epilogue s0.sp))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w16
  apply SepWP.exists_elim; intro w24; apply SepWP.exists_elim; intro w32
  apply SepWP.exists_elim; intro w40; apply SepWP.exists_elim; intro w48
  apply SepWP.exists_elim; intro w64; apply SepWP.exists_elim; intro w72
  apply SepWP.exists_elim; intro w80; apply SepWP.exists_elim; intro w88
  apply SepWP.exists_elim; intro w96; apply SepWP.exists_elim; intro w104
  apply SepWP.exists_elim; intro w112; apply SepWP.exists_elim; intro w120
  apply SepWP.exists_elim; intro w128; apply SepWP.exists_elim; intro w136
  apply SepWP.exists_elim; intro w144; apply SepWP.exists_elim; intro w152
  apply SepWP.exists_elim; intro w160; apply SepWP.exists_elim; intro w168
  apply SepWP.exists_elim; intro w176; apply SepWP.exists_elim; intro w184
  apply SepWP.exists_elim; intro w192; apply SepWP.exists_elim; intro w200
  apply SepWP.exists_elim; intro w208; apply SepWP.exists_elim; intro w216
  have hscratch_split :
      ∀ (Rest : SepProp),
        epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
        memRegion (s0.sp - 1360#64) 880 ∗
        memRegion (s0.sp - 480#64) 176 ∗
        memRegion (s0.sp - 256#64) 160 ∗ Rest ⊢
        epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
        (∃∗ t0 : BitVec 64, ∃∗ t1 : BitVec 64, ∃∗ t2 : BitVec 64, ∃∗ t3 : BitVec 64,
         ∃∗ t4 : BitVec 64, ∃∗ t5 : BitVec 64, ∃∗ t6 : BitVec 64, ∃∗ t7 : BitVec 64,
         ∃∗ t8 : BitVec 64, ∃∗ t9 : BitVec 64, ∃∗ t10 : BitVec 64, ∃∗ t11 : BitVec 64,
         ∃∗ t12 : BitVec 64, ∃∗ t13 : BitVec 64, ∃∗ t14 : BitVec 64, ∃∗ t15 : BitVec 64,
         ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
         ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
         ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
           ekReceivedScratchCells s0.sp
             t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
             u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
           memRegion (s0.sp - 1232#64) 56 ∗
           memRegion (s0.sp - 1176#64) 696 ∗
           memRegion (s0.sp - 432#64) 128 ∗
           memRegion (s0.sp - 208#64) 112) ∗ Rest := by
    intro Rest
    refine Entails.trans (Entails.of_eq (show _ =
      epilogueStagingCells s0.sp
        w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
      (memRegion (s0.sp - 1360#64) 880 ∗
       memRegion (s0.sp - 480#64) 176 ∗
       memRegion (s0.sp - 256#64) 160) ∗ Rest by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left (memRegion_ekReceived_scratch_split s0.sp))
  refine SepWP.weaken_pre (hscratch_split _) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro t0; apply SepWP.exists_elim; intro t1
  apply SepWP.exists_elim; intro t2; apply SepWP.exists_elim; intro t3
  apply SepWP.exists_elim; intro t4; apply SepWP.exists_elim; intro t5
  apply SepWP.exists_elim; intro t6; apply SepWP.exists_elim; intro t7
  apply SepWP.exists_elim; intro t8; apply SepWP.exists_elim; intro t9
  apply SepWP.exists_elim; intro t10; apply SepWP.exists_elim; intro t11
  apply SepWP.exists_elim; intro t12; apply SepWP.exists_elim; intro t13
  apply SepWP.exists_elim; intro t14; apply SepWP.exists_elim; intro t15
  apply SepWP.exists_elim; intro u0; apply SepWP.exists_elim; intro u1
  apply SepWP.exists_elim; intro u2; apply SepWP.exists_elim; intro u3
  apply SepWP.exists_elim; intro u4; apply SepWP.exists_elim; intro u5
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
  have hstep2 := ekReceivedCt1Sampled_step_60_to_1760_placed (ext := ext) s0 s1 out stA
    a0 a1 a2 a3 a4 a5 cap_ct1 ptr_ct1 s.uc.epoch s.uc.ct1.length
    t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5
    (memRegion (s0.sp - 1232#64) 56 ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
     ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     (ptr_ct1 ↦ₛ s.uc.ct1) ∗
     vecU8CloneTail A.repAlloc cap_ct1 ptr_ct1 s.uc.ct1 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392 ∗ A.pool lim st s1)
    hsp0_align hlen hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
  refine sepWP_seq_lscl hcl1 (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep2)
    fun s2 P2 hpc2 hrun2 hcl2 ⟨hvm2, hP2, _hacp2, hsp2, hx29_2, hx19_2, hx20_2, hx21_2,
      hx23_2, hx24_2, hx26_2, hx27_2, hx28_2, htr2⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm2] at hP2
  refine SepWP.weaken_pre hP2 ?_
  rw [stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)]
  have hstep3 := ekReceivedCt1Sampled_step_1760_to_2252_wp_placed hA s0 s2 st out stA
    cap_ct1 ptr_ct1 s.uc.epoch s.uc.ct1
    (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     ekReceivedScratchCells s0.sp
       a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
       u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 ∗
     memRegion (s0.sp - 1232#64) 56 ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     statesIntoPbJumpTablePlacedAt ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
     ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392)
    hfits_clone hsp0_align hlen hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx21_2 hx23_2 hx24_2
    hx26_2 hx27_2 hx28_2 htr2
  refine sepWP_seq_lscl hcl2 (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep3)
    fun s3 P3 hpc3 hrun3 hcl3 ⟨ptr_new, hP3, hsp3, hx29_3, hx19_3, hx20_3, hx21_3, hx22_3,
      hx23_3, hx24_3, hx26_3, hx27_3, hx28_3, htr3⟩ => ?_
  refine SepWP.weaken_pre hP3 ?_
  have hstep4 := ekReceivedCt1Sampled_step_2252_to_2324_placed hA s0 s3
    (M.stepEvents (ct1CloneEvents s.uc.ct1) st)
    out stA cap_ct1 ptr_ct1 ptr_new (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2
    t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5
    (vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1232#64) 56 ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     statesIntoPbJumpTablePlacedAt ∗
     memRegion out optProtoInnerStateSize ∗
     polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct1 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3
    hx26_3 hx27_3 hx28_3 htr3
  refine sepWP_seq_lscl hcl3 (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep4)
    fun s4 P4 hpc4 hrun4 hcl4 ⟨hP4, _hacp4, hsp4, hx29_4, hx19_4, hx20_4, hx21_4, hx22_4,
      hx27_4, hx28_4, htr4⟩ => ?_
  let evs_cd := ct1CloneEvents s.uc.ct1 ++ ct1DeallocEvents cap_ct1
  have hst_cd :
      M.stepEvents (ct1DeallocEvents cap_ct1) (M.stepEvents (ct1CloneEvents s.uc.ct1) st) =
      M.stepEvents evs_cd st :=
    (M.stepEvents_append (ct1CloneEvents s.uc.ct1) (ct1DeallocEvents cap_ct1) st).symm
  have hcd : Ct1CloneAndDropEnv s.uc.ct1 evs_cd :=
    ct1CloneAndDropEnv_of_dealloc s.uc.ct1 cap_ct1
  have hfits_enc : FitsEnv M lim (M.stepEvents evs_cd st) (EncoderIntoPbAllocEnv s.sending_ct1) :=
    fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv (hfits.seq_right hcd)
  rw [hst_cd] at hP4
  refine SepWP.weaken_pre hP4 ?_
  have hrecomb_stack :
      memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗ stackAt (s0.sp - 1520#64) allocHookStack =
      stackAt (s0.sp - 1520#64) encoderIntoPbStack :=
    (stackAt_encoderIntoPb_eq_allocHook (s0.sp - 1520#64)).symm
  have hstep5 := ekReceivedCt1Sampled_step_2324_to_2340_wp_cl_placed henc_cl s0 s4
    (M.stepEvents evs_cd st) out stA ptr_new
    (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch s.sending_ct1
    (((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     ekReceivedScratchCells s0.sp
       a0 a1 a2 a3 a4 a5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
       es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     epilogueStagingCells s0.sp
       w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
       w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     statesIntoPbJumpTablePlacedAt ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392)
    hcl4 hfits_enc hsp0_align hpc4 hrun4 hsp4 hx29_4 hx19_4 hx20_4 hx21_4 hx22_4 hx27_4 hx28_4 htr4
  refine SepWP.seq
    (SepWP.weaken_pre (by rw [← hrecomb_stack]; exact Entails.of_eq (by sep_ac_rfl)) hstep5) ?_
  intro s5 P5 hpc5 hrun5 ⟨evs_enc, e0, e1, e2, e3, e4, e5, e6, henc_env, _hacp5, hP5,
    hsp5, hx29_5, hx19_5, hx20_5, hx21_5, hx22_5, hx27_5, hx28_5, htr5⟩
  let evs_tot := evs_cd ++ evs_enc
  have hst_tot :
      M.stepEvents evs_enc (M.stepEvents evs_cd st) = M.stepEvents evs_tot st :=
    (M.stepEvents_append evs_cd evs_enc st).symm
  have htot_env : EkReceivedCt1SampledEnv s evs_tot :=
    ekReceivedCt1SampledEnv_of_parts hcd henc_env
  rw [hst_tot] at hP5
  refine SepWP.weaken_pre hP5 ?_
  have hstep6 := ekReceivedCt1Sampled_step_2340_to_1544_placed (ext := ext) s0 s5 out stA ptr_new
    (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
    a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2
    e0 e1 e2 e3 e4 e5 e6
    t6 t7 t8 t9 t10 t11 t12 t13 t14 t15
    w8 w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120
    w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216
    (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     memRegion (stA + 8#64) polyEncoderSize ∗
     A.pool lim (M.stepEvents evs_tot st) s5 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
     ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
     ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
     ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
     ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (s0.sp - 1176#64) 696 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 10#64) ∗
     statesIntoPbJumpTablePlacedAt ∗
     memRegion out optProtoInnerStateSize ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     memRegion (stA + 536#64) 392)
    hsp0_align hpc5 hrun5 hsp5 hx29_5 hx19_5 hx20_5 hx21_5 hx22_5 hx27_5 hx28_5 htr5
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep6) ?_
  intro s6 P6 hpc6 hrun6 ⟨hvm6, hP6, _hacp6, hsp6, hx29_6, hx19_6, hx21_6, hx22_6, htr6⟩
  rw [← A.pool_of_vmPreserved hvm6] at hP6
  refine SepWP.weaken_pre hP6 ?_
  have hscratch := ekReceivedScratchCells_entails_memRegions s0.sp
    es0 es1 es2 ek0 ek1 ek2 t6 ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
    a0 a1 a2 a3 a4 a5 s.uc.epoch
    es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5
    e0 e1 e2 e3 e4 e5 e6
  have hstA := stA_ekReceivedCt1Sampled_entails_928 stA
    a0 a1 a2 a3 a4 a5 es0 es1 es2 ek0 ek1 ek2
    cap_ct1 ptr_ct1 (BitVec.ofNat 64 s.uc.ct1.length) s.uc.epoch
  have hpre_epi :
      ekReceivedScratchCells s0.sp
        es0 es1 es2 ek0 ek1 ek2 t6 ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
        a0 a1 a2 a3 a4 a5 s.uc.epoch
        es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
      (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
       ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
       ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
       ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
      epilogueStagingCells s0.sp
        es0 es1 es2 ek0 ek1 ek2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch e0 e1 e2 e3 e4 e5 e6
        w192 w200 w208 w216 ∗
      (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       memRegion (stA + 8#64) polyEncoderSize ∗
       A.pool lim (M.stepEvents evs_tot st) s6 ∗
       stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
       ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 1176#64) 696 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 10#64) ∗
       statesIntoPbJumpTablePlacedAt ∗
       memRegion out optProtoInnerStateSize ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
       memRegion (stA + 536#64) 392) ⊢
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        es0 es1 es2 ek0 ek1 ek2
        ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
        s.uc.epoch e0 e1 e2 e3 e4 e5 e6
        w192 w200 w208 w216 ∗
      memRegion (s0.sp - 1360#64) 880 ∗
      memRegion (s0.sp - 480#64) 176 ∗
      memRegion (s0.sp - 256#64) 160 ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      A.pool lim (M.stepEvents evs_tot st) s6 ∗
      (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       memRegion stA chunkedStatesSize ∗
       statesIntoPbJumpTablePlacedAt) := by
    refine Entails.trans (Entails.of_eq (show _ =
      (ekReceivedScratchCells s0.sp
         es0 es1 es2 ek0 ek1 ek2 t6 ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
         a0 a1 a2 a3 a4 a5 s.uc.epoch
         es0 es1 es2 ek0 ek1 ek2 a0 a1 a2 a3 a4 a5 ∗
       (((s0.sp - 1232#64) ↦₆₄ e0) ∗ ((s0.sp - 1224#64) ↦₆₄ e1) ∗
        ((s0.sp - 1216#64) ↦₆₄ e2) ∗ ((s0.sp - 1208#64) ↦₆₄ e3) ∗
        ((s0.sp - 1200#64) ↦₆₄ e4) ∗ ((s0.sp - 1192#64) ↦₆₄ e5) ∗
        ((s0.sp - 1184#64) ↦₆₄ e6)) ∗
       memRegion (s0.sp - 1176#64) 696 ∗
       memRegion (s0.sp - 432#64) 128 ∗
       memRegion (s0.sp - 208#64) 112) ∗
      ((stA ↦₆₄ 10#64) ∗
       memRegion (stA + 8#64) polyEncoderSize ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ es0) ∗ ((stA + 464#64) ↦₆₄ es1) ∗ ((stA + 472#64) ↦₆₄ es2) ∗
       ((stA + 480#64) ↦₆₄ ek0) ∗ ((stA + 488#64) ↦₆₄ ek1) ∗ ((stA + 496#64) ↦₆₄ ek2) ∗
       ((stA + 504#64) ↦₆₄ cap_ct1) ∗ ((stA + 512#64) ↦₆₄ ptr_ct1) ∗
       ((stA + 520#64) ↦₆₄ BitVec.ofNat 64 s.uc.ct1.length) ∗
       ((stA + 528#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (stA + 536#64) 392) ∗
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       epilogueStagingCells s0.sp
         es0 es1 es2 ek0 ek1 ek2
         ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
         s.uc.epoch e0 e1 e2 e3 e4 e5 e6
         w192 w200 w208 w216 ∗
       statesIntoPbSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗
       A.pool lim (M.stepEvents evs_tot st) s6 ∗
       protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
       vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
       vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
         (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
       statesIntoPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hscratch (sepConj_mono hstA (Entails.refl _))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  have hep := states_into_pb_epilogue_placed (ext := ext) A lim (M.stepEvents evs_tot st)
    s0 s6 out
    es0 es1 es2 ek0 ek1 ek2
    ptr_new (BitVec.ofNat 64 s.uc.ct1.length) a0 a1 a2 a3 a4 a5
    s.uc.epoch e0 e1 e2 e3 e4 e5 e6
    w192 w200 w208 w216
    (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1 ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTablePlacedAt)
    hsp0_align hpc6 hrun6 hsp6 hx29_6 hx19_6 htr6
  rw [hx22_6, hx21_6] at hep
  refine SepWP.mono (SepWP.weaken_pre hpre_epi hep) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f, _hvm_f⟩
  refine ⟨⟨evs_tot, hEnv evs_tot htot_env, ?_⟩, hsp_f, hcs_f, htr_f⟩
  refine Entails.trans hPf ?_
  have hout := outWords28_entails_ekReceivedCt1Sampled A.repAlloc out
    es0 es1 es2 ek0 ek1 ek2
    (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
    a0 a1 a2 a3 a4 a5
    e0 e1 e2 e3 e4 e5 e6
    w192 w200 w208 w216 s
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
       0x8000000000000008#64
       es0 es1 es2 ek0 ek1 ek2
       (BitVec.ofNat 64 s.uc.ct1.length) ptr_new (BitVec.ofNat 64 s.uc.ct1.length)
       a0 a1 a2 a3 a4 a5 s.uc.epoch
       e0 e1 e2 e3 e4 e5 e6
       w192 w200 w208 w216 ∗
     protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct1.intoPb ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc es0 es1 es2 s.uc.es ∗
     vecU8Heap A.repAlloc ek0 ek1 ek2 s.uc.ek ∗
     vecU8Heap A.repAlloc (BitVec.ofNat 64 s.uc.ct1.length) ptr_new
       (BitVec.ofNat 64 s.uc.ct1.length) s.uc.ct1) ∗
    (memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTablePlacedAt ∗
     A.pool lim (M.stepEvents evs_tot st) sf ∗
     stackAt s0.sp statesIntoPbStack) by sep_ac_rfl)) ?_
  exact sepConj_mono_left hout

/-- Tight `EkReceivedCt1SampledEnv` `withLsCodeLoaded` relocatable `subroutine_ok` for Arm 8
    (`States.ekReceivedCt1Sampled`) taking `withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)`. -/
theorem states_into_pb_ekReceivedCt1Sampled_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbEkReceivedCt1SampledPlacedSpec M A lim F s)) :=
  states_into_pb_ekReceivedCt1Sampled_of_env_cl_placed hA henc_cl s (fun _ h => h)

/-- Verifies `<States>::into_pb`
    (Block `334`) on `.ekReceivedCt1Sampled s` (Arm 8, tag `10`). -/
theorem states_into_pb_ekReceivedCt1Sampled_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbEkReceivedCt1SampledPlacedSpec M A lim F s)) :=
  states_into_pb_ekReceivedCt1Sampled_env_cl_placed hA henc_cl s

/-- Default `statesIntoPbVariantPlacedSpec` (`SpqrBoundedEvs 64 (2 * |encodeRaw| + 1024)`)
    `withLsCodeLoaded` relocatable `subroutine_ok` for Arm 8 (`States.ekReceivedCt1Sampled`)
    taking `withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)` under explicit payload/slot
    size bounds. -/
theorem states_into_pb_ekReceivedCt1Sampled_of_bounds_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (hcnt : 3 + (encoderIntoPbVecs s.sending_ct1).length ≤ 64)
    (hct1_max : s.uc.ct1.length ≤ MallocngMaxAllocSize)
    (hct1_req : s.uc.ct1.length ≤
      2 * (V1State.encodeRaw (States.ekReceivedCt1Sampled (P := spqrPolyApi) s).into_pb).length + 1024)
    (hslots : ∀ cs ∈ encoderIntoPbVecs s.sending_ct1,
      2 * cs.length ≤ MallocngMaxAllocSize ∧
      2 * cs.length ≤
        2 * (V1State.encodeRaw (States.ekReceivedCt1Sampled (P := spqrPolyApi) s).into_pb).length + 1024) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpec M A lim F (.ekReceivedCt1Sampled s))) :=
  states_into_pb_ekReceivedCt1Sampled_of_env_cl_placed hA henc_cl s
    (fun _ => ekReceivedCt1SampledEnv_imp_spqrBoundedEvs hcnt (by omega) hct1_max hct1_req hslots)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aClPlacedBudget
