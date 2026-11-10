/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7cPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7fPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7g
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7gPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part G

Lifts the `s.sendingCt1 = none` cleanup (`+3552 -> +7100 -> +4632`), `<PolyEncoder>::from_pb` copy
and call (`+3652 -> +3716 -> lsmpl.base 374`), and `<PolyEncoder>::from_pb = Err` cleanup
(`+3720 -> +3732 -> +4632`) to `VmPreserved` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7gPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 ls_blockPlacement_base lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialError ProtoPolynomialDecoder ProtoPolynomialEncoder spqrAuthApi)
open CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt (Ct1Sent)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.Drop
  (none2Cap_add_two_beq_zero noneCap_add_two_beq_zero vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (protoPolynomialEncoderAt resultPolyEncoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved v7_1888_tag_392_to_memRegion_400 v7_ct1SentAt_unpack v7_ct1SentHeap
   v7_ct1SentHeap_entails_dealloc v7_ct1SentOtherCells v7_ct1SentSpillCells v7_ct1SentWordsAt
   v7_ct1SentWordsAt_1264_eq_spill_other v7_ct1SentWordsAt_entails_128
   v7_optProtoPolyEncoderTail v7_resultPolyEncoder_err_entails_tag_392)
open CryptoVerification.SpqrV1.Unchunked
  (ct1SentAt extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (FromPbAllocHooksPlacedBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2 (seq_clean_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (blk333_noSvc0 entails_pre_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bPlacedBudget
  (v7_optDecoderCapProp v7_optProtoPolyDecoderTail)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7cPlacedBudget
  (v7_cleanup_3732_of_placedHooks v7_cleanup_7100_of_placedHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7fPlacedBudget
  (v7_uc_ok_spill_3552_to_7100_placed_budget)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

local macro "wp_steps_sync_333 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException _))
    blkLib_eq_333 blk333_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## 1. `s.sendingCt1 = none` Path (`+3552 -> +7100 -> +4632`) -/

/-- Budget-threaded `s.sendingCt1 = none` cleanup path (`+3552 -> +7100 -> +4632`, Block `333`)
    under `FromPbAllocHooksPlacedBudget`: when `<Ct1Sent>::from_pb` returns `Ok(uc)` at
    `fsp + 1888..2016` and `[pbA + 128] = noneCap`, spills `uc` to `fsp + 1264..1392`, branches
    to `+7100`, deallocates all 5 vectors of `uc` and `optDec`, and reaches `+4632` under
    `FreeOnlyEvs`. -/
theorem v7_uc_ok_none_enc_3552_to_4632_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (uc : Ct1Sent (spqrAuthApi F)) (optDec : Option ProtoPolynomialDecoder)
    (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ct1SentAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) uc ∗
        memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
        ((pbA + 128#64) ↦₆₄ noneCap) ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          ((pbA + 128#64) ↦₆₄ noneCap) ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left
      (v7_ct1SentAt_unpack A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) uc))) ?_
  wp_conv_pre =>
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro c1
  apply ProofLib.SepWP.exists_left; intro p1
  apply ProofLib.SepWP.exists_left; intro l1
  apply ProofLib.SepWP.exists_left; intro c2
  apply ProofLib.SepWP.exists_left; intro p2
  apply ProofLib.SepWP.exists_left; intro l2
  apply ProofLib.SepWP.exists_left; intro c3
  apply ProofLib.SepWP.exists_left; intro p3
  apply ProofLib.SepWP.exists_left; intro l3
  apply ProofLib.SepWP.exists_left; intro c4
  apply ProofLib.SepWP.exists_left; intro p4
  apply ProofLib.SepWP.exists_left; intro l4
  apply ProofLib.SepWP.exists_left; intro c5
  apply ProofLib.SepWP.exists_left; intro p5
  apply ProofLib.SepWP.exists_left; intro l5
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
    (⌜c1.toNat < 2 ^ 63⌝ ∗
     (v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1888#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
      memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
      ((pbA + 128#64) ↦₆₄ noneCap) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
       A.pool lim st s1 ∗ Frame))) by sep_ac_rfl))
    (sepConj_mono_left (v7_ct1SentHeap_entails_dealloc A.repAlloc uc
      c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5))) ?_
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜c1.toNat < 2 ^ 63⌝ ∗
    (v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1888#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
     memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
     ((pbA + 128#64) ↦₆₄ noneCap) ∗
     ((stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
        vecCapPtrDealloc A.repAlloc c5 p5) ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
       Frame) ∗ A.pool lim st s1)) by sep_ac_rfl)) ?_
  apply ProofLib.SepWP.pure_elim; intro hc1
  let Frame_spill : SepProp :=
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
    (vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
     vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
     vecCapPtrDealloc A.repAlloc c5 p5) ∗
    (((pbA + 184#64) ↦₆₄ cap_dec) ∗
     v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
    Frame
  refine seq_clean_st
    (mid := lsmpl.base 333 + 7100#64)
    (P_mid := fun sm =>
      memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
      v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
      ((pbA + 128#64) ↦₆₄ noneCap) ∗
      Frame_spill ∗
      A.pool lim st sm)
    (Q := fun sm =>
      VmPreserved s1 sm ∧
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x1 = c1 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x24 = c2 ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = p1 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [Frame_spill]))
      (v7_uc_ok_spill_3552_to_7100_placed_budget A lim st s0 s1 (s0.sp - 2400#64) out pbA cap_dec
        c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch Frame_spill
        hfsp_align hc1 hpc1 hrun1 hsp1 hx19_1 hx22_1 hx27_1 htr1)
  · intro s2 hpc2 hrun2 ⟨_hvm, hsp2, hx1_2, hx19_2, hx22_2, hx24_2, hx27_2, hx28_2, htr2⟩
    dsimp only [Frame_spill]
    rw [v7_ct1SentWordsAt_1264_eq_spill_other]
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono
        (v7_cleanup_7100_of_placedHooks hA s0 s2 out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 optDec st
          (v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch ∗
           memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
           ((pbA + 128#64) ↦₆₄ noneCap) ∗ Frame)
          hcap_dec hsp0_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx22_2 hx24_2 hx27_2 hx28_2 htr2) ?_)
    intro s3 P3 _hrun3 _hpc3 ⟨evs, hevs, hP3, hq⟩
    refine ⟨evs, hevs, Entails.trans hP3 ?_, hq⟩
    have h1264 :
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch ⊢
        memRegion ((s0.sp - 2400#64) + 1264#64) 128 := by
      rw [← v7_ct1SentWordsAt_1264_eq_spill_other]
      exact v7_ct1SentWordsAt_entails_128 ((s0.sp - 2400#64) + 1264#64)
        c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch
    refine Entails.trans (Entails.of_eq (show _ =
      (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
       v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
       ((pbA + 128#64) ↦₆₄ noneCap) ∗
       memRegion (pbA + 184#64) 40 ∗
       A.pool lim (M.stepEvents evs st) s3 ∗
       Frame) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h1264) (Entails.of_eq (by sep_ac_rfl))

/-- Budget-threaded `s.sendingCt1 = none` cleanup path (`+3552 -> +7100 -> +4632`, Block `333`)
    under `FromPbAllocHooksBudget`. -/
theorem v7_uc_ok_none_enc_3552_to_4632_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (uc : Ct1Sent (spqrAuthApi F)) (optDec : Option ProtoPolynomialDecoder)
    (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ct1SentAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) uc ∗
        memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
        ((pbA + 128#64) ↦₆₄ noneCap) ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          ((pbA + 128#64) ↦₆₄ noneCap) ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) :=
  v7_uc_ok_none_enc_3552_to_4632_of_placedHooks hA.toPlacedBudget
    s0 s1 out pbA cap_dec uc optDec st Frame
    hcap_dec hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx27_1 htr1

/-! ## 2. `<PolyEncoder>::from_pb` Copy (`+3652 -> +3716`) and Call (`+3716 -> lsmpl.base 374`) -/

/-- `VmPreserved`-strengthened copy of `ProtoPolynomialEncoder` (`56` B) from `pbA + 128` to
    `fsp + 1792` (`sp + 0x700`), storing `c1` (`x1`) to `[sp, #0x18]` and setting
    `x0 = fsp + 1888`, `x1 = fsp + 1792`, `x20 = fsp + 1792`, `x25 = fsp + 1888` at
    `+3652 -> +3716` (Block `333`). -/
theorem v7_copy_enc_3652_to_3716_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_enc cap_dec c1 c2 l1 p1 x21_val x23_val slot24_old : BitVec 64)
    (encPb : ProtoPolynomialEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3652#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx1_1 : s1.readReg64 .x1 = c1)
    (hx8_1 : s1.readReg64 .x8 = cap_enc)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3716#64) s1
      (((pbA + 128#64) ↦₆₄ cap_enc) ∗
        v7_optProtoPolyEncoderTail A (pbA + 128#64) cap_enc (some encPb) ∗
        memRegion (fsp + 1792#64) 56 ∗
        ((fsp + 24#64) ↦₆₄ slot24_old) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (pbA + 128#64) 56 ∗
          protoPolynomialEncoderAt A (fsp + 1792#64) encPb ∗
          ((fsp + 24#64) ↦₆₄ c1) ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1792#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = fsp + 1792#64 ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = fsp + 1888#64 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = p1 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v7_copy_enc_3652_to_3716_placed
      (A := A) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out pbA cap_enc cap_dec c1 c2 l1 p1 x21_val x23_val slot24_old encPb Frame
      hfsp_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx1_1) (by simpa using hx8_1) (by simpa using hx19_1)
      (by simpa using hx21_1) (by simpa using hx22_1) (by simpa using hx23_1)
      (by simpa using hx24_1) (by simpa using hx25_1) (by simpa using hx26_1)
      (by simpa using hx27_1) (by simpa using hx28_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m,
       hx25_m, hx26_m, hx27_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx19_m, by simpa using hx20_m, by simpa using hx21_m,
       by simpa using hx22_m, by simpa using hx23_m, by simpa using hx24_m,
       by simpa using hx25_m, by simpa using hx26_m, by simpa using hx27_m,
       by simpa using hx28_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v7_copy_enc_3652_to_3716_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_enc cap_dec c1 c2 l1 p1 x21_val x23_val slot24_old : BitVec 64)
    (encPb : ProtoPolynomialEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3652#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx1_1 : s1.readReg64 .x1 = c1)
    (hx8_1 : s1.readReg64 .x8 = cap_enc)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3716#64) s1
      (((pbA + 128#64) ↦₆₄ cap_enc) ∗
        v7_optProtoPolyEncoderTail A.repAlloc (pbA + 128#64) cap_enc (some encPb) ∗
        memRegion (fsp + 1792#64) 56 ∗
        ((fsp + 24#64) ↦₆₄ slot24_old) ∗
        Frame ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (pbA + 128#64) 56 ∗
          protoPolynomialEncoderAt A.repAlloc (fsp + 1792#64) encPb ∗
          ((fsp + 24#64) ↦₆₄ c1) ∗
          Frame ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1792#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = fsp + 1792#64 ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = fsp + 1888#64 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = p1 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v7_copy_enc_3652_to_3716_placed (A := A.repAlloc) (ext := ext)
    s0 s1 fsp out pbA cap_enc cap_dec c1 c2 l1 p1 x21_val x23_val slot24_old encPb
    (Frame ∗ A.pool lim st s1)
    hfsp_align hpc1 hrun1 hsp1 hx1_1 hx8_1 hx19_1 hx21_1 hx22_1 hx23_1
    hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- `VmPreserved`-strengthened `bl` instruction at `+3716` to `<PolyEncoder>::from_pb` entry
    (`lsmpl.base 374`), setting `x30 = lsmpl.base 333 + 3720`. -/
theorem v7_bl_encoder_3716_to_32996_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_dec c2 l1 p1 x21_val x23_val : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 3716#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = fsp + 1888#64)
    (hx1_1 : s1.readReg64 .x1 = fsp + 1792#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = fsp + 1792#64)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1888#64)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374) s1 P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1792#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = fsp + 1792#64 ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = fsp + 1888#64 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = p1 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 3720#64 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v7_bl_encoder_3716_to_32996_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out pbA cap_dec c2 l1 p1 x21_val x23_val P
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx0_1) (by simpa using hx1_1) (by simpa using hx19_1)
      (by simpa using hx20_1) (by simpa using hx21_1) (by simpa using hx22_1)
      (by simpa using hx23_1) (by simpa using hx24_1) (by simpa using hx25_1)
      (by simpa using hx26_1) (by simpa using hx27_1) (by simpa using hx28_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m,
       hx25_m, hx26_m, hx27_m, hx28_m, hx30_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx19_m, by simpa using hx20_m, by simpa using hx21_m,
       by simpa using hx22_m, by simpa using hx23_m, by simpa using hx24_m,
       by simpa using hx25_m, by simpa using hx26_m, by simpa using hx27_m,
       by simpa using hx28_m, by simpa using hx30_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v7_bl_encoder_3716_to_32996_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_dec c2 l1 p1 x21_val x23_val : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 3716#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = fsp + 1888#64)
    (hx1_1 : s1.readReg64 .x1 = fsp + 1792#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = fsp + 1792#64)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1888#64)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374) s1
      (P ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢ P ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1792#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = fsp + 1792#64 ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = fsp + 1888#64 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = p1 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 3720#64 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v7_bl_encoder_3716_to_32996_placed (ext := ext)
    s0 s1 fsp out pbA cap_dec c2 l1 p1 x21_val x23_val (P ∗ A.pool lim st s1)
    hpc1 hrun1 hsp1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-! ## 3. `<PolyEncoder>::from_pb = Err` Cleanup (`+3720 -> +3732 -> +4632`) -/

/-- Budget-threaded `<PolyEncoder>::from_pb = Err` cleanup (`+3720 -> +3732 -> +4632`, Block `333`)
    under `FromPbAllocHooksPlacedBudget`: steps `+3720 -> +3732`, deallocates all 5 vectors of `uc`
    and `optDec` via `v7_cleanup_3732_of_placedHooks`, and reaches `+4632` under `FreeOnlyEvs`. -/
theorem v7_enc_err_3720_to_4632_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (uc : Ct1Sent (spqrAuthApi F))
    (err : PolynomialError) (optDec : Option ProtoPolynomialDecoder)
    (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3720#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) (.error err) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
          (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono
      (v7_resultPolyEncoder_err_entails_tag_392 A.repAlloc (s0.sp - 2400#64) err)
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (v7_ct1SentHeap_entails_dealloc A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5)))))) ?_
  refine seq_clean_st
    (mid := lsmpl.base 333 + 3732#64)
    (P_mid := fun sm =>
      memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
       (vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
        vecCapPtrDealloc A.repAlloc c5 p5) ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
       A.pool lim st sm ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x24 = c2 ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = p1 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · have h1888 : (s0.sp - 2400#64) + 1888#64 = s0.sp - 512#64 := by bv_omega
    have h1896 : (s0.sp - 2400#64) + 1896#64 = s0.sp - 504#64 := by bv_omega
    have h400 := v7_1888_tag_392_to_memRegion_400 (s0.sp - 2400#64) 2#64
    rw [h1888, h1896] at h400 ⊢
    rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 3720#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 3732#64) s1 _ _
    wp_steps_sync_333 ((blkPl_333).base + 3732#64)
    try simp only [State.setMem_setMem]
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      refine Entails.trans (Entails.of_eq (show _ =
        (((s0.sp - 512#64) ↦₆₄ 2#64) ∗ memRegion (s0.sp - 504#64) 392) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
         v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
         (vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
          vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
          vecCapPtrDealloc A.repAlloc c5 p5) ∗
         (((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
         A.pool lim st _ ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left h400) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx24_2, hx27_2, hx28_2, htr2⟩
    rw [v7_ct1SentWordsAt_1264_eq_spill_other]
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono
        (v7_cleanup_3732_of_placedHooks hA s0 s2 out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 optDec st
          (v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch ∗
           memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ Frame)
          hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx24_2 hx27_2 hx28_2 htr2) ?_)
    intro s3 P3 _hrun3 _hpc3 ⟨evs, hevs, hP3, hq⟩
    refine ⟨evs, hevs, Entails.trans hP3 ?_, hq⟩
    have h1264 :
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch ⊢
        memRegion ((s0.sp - 2400#64) + 1264#64) 128 := by
      rw [← v7_ct1SentWordsAt_1264_eq_spill_other]
      exact v7_ct1SentWordsAt_entails_128 ((s0.sp - 2400#64) + 1264#64)
        c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch
    refine Entails.trans (Entails.of_eq (show _ =
      (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
       v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       memRegion (pbA + 184#64) 40 ∗
       A.pool lim (M.stepEvents evs st) s3 ∗
       Frame) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h1264) (Entails.of_eq (by sep_ac_rfl))

/-- Budget-threaded `<PolyEncoder>::from_pb = Err` cleanup (`+3720 -> +3732 -> +4632`, Block `333`)
    under `FromPbAllocHooksBudget`. -/
theorem v7_enc_err_3720_to_4632_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (uc : Ct1Sent (spqrAuthApi F))
    (err : PolynomialError) (optDec : Option ProtoPolynomialDecoder)
    (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3720#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) (.error err) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A.repAlloc uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
          (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) :=
  v7_enc_err_3720_to_4632_of_placedHooks hA.toPlacedBudget
    s0 s1 out pbA cap_dec c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
    uc err optDec st Frame
    hcap_dec hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx24_1 hx27_1 hx28_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7gPlacedBudget
