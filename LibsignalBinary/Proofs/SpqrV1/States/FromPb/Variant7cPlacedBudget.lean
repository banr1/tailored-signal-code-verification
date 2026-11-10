/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7c
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7cPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part C

Relocatable budget-threaded mid-stage cleanup paths (`+7196`, `+7100`, `+3732`, and
`+10556 -> +11112 -> +4632`) under `FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7cPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_333 blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 ls_blockPlacement_base lsmpl lsρ withMemEq)
open CryptoVerification.LibsignalSpqrV1 (GF16 NUM_POLYS PolyEncoder ProtoPolynomialDecoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop
  (DropGluePoly16Ghost dropGluePoly16Stack dropStack32
   optProtoPolyDecoder_none_entails_memRegion_40 polyEncoderAt_entails_tag_vecs_tail
   vecCapPtrDealloc vecGF16ListOf)
open CryptoVerification.SpqrV1.Poly (polyArrayBytes polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb (TraceCalleeSaved)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
   RustCliAllocBudget rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (dropGluePoly16Spec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs seq_clean_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux (seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4PlacedBudget
  (v4_ptsCap_add_one_ne_zero v4_stackAt_allocHook_to_encoderFromPbStack
   v4_stackAt_encoderFromPbStack_to_allocHook v4_sub_ok_dealloc_125316_fo_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aPlacedBudget
  (v7_proto_decoder_dealloc_4556_of_placedHooks v7_sub_ok_drop_poly16_mem_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bPlacedBudget
  (v7_cleanup_11112_placed_budget v7_cleanup_opt_decoder_some_pre_pool v7_optDecoderCapProp
   v7_optProtoPolyDecoderTail v7_stackAt_dropStack32_to_encoderFromPbStack
   v7_stackAt_encoderFromPbStack_to_dropStack32)

/-! ## Re-exports of Pure Predicates & Join Helpers from `Variant7c` -/

abbrev v7_ct1SentSpillCells := CryptoVerification.SpqrV1.States.FromPb.v7_ct1SentSpillCells

alias v7_polyEncoder_1392_join := CryptoVerification.SpqrV1.States.FromPb.v7_polyEncoder_1392_join
alias v7_drop_poly16_pre := CryptoVerification.SpqrV1.States.FromPb.v7_drop_poly16_pre

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

private theorem blk333_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_333.text = true := by
  decide +kernel

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

private theorem entails_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (hent : ∀ sc : State, sc = s → P ⊢ P_mid sc)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  SepWP.weaken_pre (hent s rfl) h

private theorem sepWP_with_evs {prog : Program} {target : BitVec 64} {s : State}
    (evs : List AllocEvent) (hevs : FreeOnlyEvs evs)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs evs sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs', FreeOnlyEvs evs' ∧ (Pm ⊢ P_evs evs' sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs, hevs, hp, hq⟩

private theorem seq_evs_st {M : AllocCostModel}
    {prog : Program} {mid target : BitVec 64} {s1 : State} (st : M.σ)
    {Pre : SepProp} (P_mid P_post : M.σ → State → SepProp)
    (Q_mid : State → Prop) {Q_post : State → Prop}
    (h1 : SepWP prog mid s1 Pre (fun sm Pm =>
      ∃ evs1, FreeOnlyEvs evs1 ∧ (Pm ⊢ P_mid (M.stepEvents evs1 st) sm) ∧ Q_mid sm))
    (h2 : ∀ (st1 : M.σ) (s2 : State),
      s2.pc = mid → s2.status = .Running → Q_mid s2 →
      SepWP prog target s2 (P_mid st1 s2) (fun sf Pf =>
        ∃ evs2, FreeOnlyEvs evs2 ∧ (Pf ⊢ P_post (M.stepEvents evs2 st1) sf) ∧ Q_post sf)) :
    SepWP prog target s1 Pre (fun sf Pf =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pf ⊢ P_post (M.stepEvents evs st) sf) ∧ Q_post sf) := by
  refine seq_clean_evs (P_evs := fun evs1 sm => P_mid (M.stepEvents evs1 st) sm) (Q := Q_mid) h1 ?_
  intro evs1 s2 hevs1 hpc2 hrun2 hq2
  refine SepWP.mono (h2 (M.stepEvents evs1 st) s2 hpc2 hrun2 hq2) ?_
  intro sf _Pf _ _ ⟨evs2, hevs2, hPf, hqf⟩
  refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hqf⟩
  rw [AllocCostModel.stepEvents_append]
  exact hPf

/-! ## 1. Cleanup at `+7100..+7208 -> +4632` and `+3732..+3740 -> +7104/+7116` -/

/-- Budget-threaded placed step `+7196 -> +4632` under `FromPbAllocHooksPlacedBudget`:
sets `x28 = 0#64` and deallocates `optDec` at `pbA + 184#64` if `some` under `FreeOnlyEvs`. -/
theorem v7_cleanup_7196_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7196#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  cases optDec with
  | none =>
    unfold v7_optDecoderCapProp CryptoVerification.SpqrV1.States.FromPb.v7_optDecoderCapProp at hcap_dec
    subst hcap_dec
    unfold v7_optProtoPolyDecoderTail CryptoVerification.SpqrV1.States.FromPb.v7_optProtoPolyDecoderTail
    dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx22_1 ⊢
    rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 7196#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4632#64) s1 _ _
    apply sepWP_evs_nil
    simp only [AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 4632#64)
    try simp only [State.setMem_setMem]
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      have hm := optProtoPolyDecoder_none_entails_memRegion_40 (pbA + 184#64)
      dsimp only [noneCap] at hm
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 184#64) ↦₆₄ 18446744073709551615#64) ∗
           memRegion ((pbA + 184#64) + 8#64) 32) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool lim st _ ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  | some pb =>
    refine SepWP.weaken_pre
      (v7_cleanup_opt_decoder_some_pre_pool A.repAlloc (s0.sp - 2400#64) pbA cap_dec pb
        (A.pool lim st s1) Frame) ?_
    apply ProofLib.SepWP.exists_left; intro ptsPtr
    apply ProofLib.SepWP.pure_elim; rintro ⟨hpts_le, hpts_cap_lt, _⟩
    dsimp only [RustCliAllocBudget.repAlloc_live]
    refine seq_clean_st
      (mid := lsmpl.base 333 + 4556#64)
      (P_mid := fun sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
         (if cap_dec = 0 then emp
          else A.live ptsPtr (cap_dec.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
              ((cap_dec.toNat - pb.pts.length) * 24)) ∗
         memRegion (pbA + 208#64) 16) ∗
        A.pool lim st sm ∗ Frame)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) ?_ ?_
    · have hne := v4_ptsCap_add_one_ne_zero hpts_cap_lt
      rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 7196#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4556#64) s1 _ _
      wp_steps_sync_333 ((blkPl_333).base + 4556#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
      exact v7_proto_decoder_dealloc_4556_of_placedHooks hA s0 s2 out pbA cap_dec ptsPtr 0#64
        pb.pts st Frame hsp0_align hpts_le hpts_cap_lt hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2

/-- Budget-threaded placed step `+7196 -> +4632` under `FromPbAllocHooksBudget`. -/
theorem v7_cleanup_7196_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7196#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) :=
  v7_cleanup_7196_of_placedHooks hA.toPlacedBudget s0 s1 out pbA cap_dec optDec st Frame
    hcap_dec hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx27_1 htr1

/-- Budget-threaded placed deallocation of the 4 `Vec<u8>` buffers `c2/p2 .. c5/p5` at
`+7116 -> +7196` under `FromPbAllocHooksPlacedBudget`. -/
theorem v7_dealloc_4vecs_7116_to_7196_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7116#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7196#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
        vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc_fo := v4_sub_ok_dealloc_125316_fo_placed hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  unfold v7_ct1SentSpillCells CryptoVerification.SpqrV1.States.FromPb.v7_ct1SentSpillCells
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  have h1296 : (s0.sp - 2400#64) + 1296#64 = s0.sp - 1104#64 := by bv_omega
  have h1312 : (s0.sp - 2400#64) + 1312#64 = s0.sp - 1088#64 := by bv_omega
  have h1320 : (s0.sp - 2400#64) + 1320#64 = s0.sp - 1080#64 := by bv_omega
  have h1336 : (s0.sp - 2400#64) + 1336#64 = s0.sp - 1064#64 := by bv_omega
  have h1344 : (s0.sp - 2400#64) + 1344#64 = s0.sp - 1056#64 := by bv_omega
  have h1360 : (s0.sp - 2400#64) + 1360#64 = s0.sp - 1040#64 := by bv_omega
  have h1368 : (s0.sp - 2400#64) + 1368#64 = s0.sp - 1032#64 := by bv_omega
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst; rw [h7552, h1296, h1312, h1320, h1336, h1344, h1360, h1368]
  dsimp only [vecCapPtrDealloc, RustCliAllocBudget.repAlloc, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
  let P_post : M.σ → State → SepProp := fun stf sm =>
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      A.pool lim stf sm ∗ Frame
  refine seq_evs_st st (mid := lsmpl.base 333 + 7136#64)
    (fun st1 sm =>
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c3 == 0#64) = true then emp else A.live p3 c3.toNat 1 ∗ memRegion p3 c3.toNat) ∗
      (if (c4 == 0#64) = true then emp else A.live p4 c4.toNat 1 ∗ memRegion p4 c4.toNat) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool lim st1 sm ∗ Frame)
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 7116#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7136#64) s1 _ _
    by_cases hc2 : (c2 == 0#64) = true <;>
      simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 7136#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := hsp1 ▸ hfsp_align
      apply sepWP_evs_dealloc c2.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      try simp only [State.setMem_setMem]
      rw [show stackAt (s0.sp - 2400#64) allocHookStack = stackAt s1.sp allocHookStack from hsp1 ▸ rfl]
      wp_call hdealloc_fo (p2, c2.toNat, 1, st)
      rw [hsp1]
      have hacp : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s1.sp›.trans hsp1
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr1.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  intro st2 s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, htr2⟩
  refine seq_evs_st st2 (mid := lsmpl.base 333 + 7156#64)
    (fun st3 sm =>
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c4 == 0#64) = true then emp else A.live p4 c4.toNat 1 ∗ memRegion p4 c4.toNat) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool lim st3 sm ∗ Frame)
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc2 ⊢
    change s2.pc = (blkPl_333).base + 7136#64 at hpc2
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7156#64) s2 _ _
    by_cases hc3 : (c3 == 0#64) = true <;>
      simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 7156#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
      apply sepWP_evs_dealloc c3.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      try simp only [State.setMem_setMem]
      rw [show stackAt (s0.sp - 2400#64) allocHookStack = stackAt s2.sp allocHookStack from hsp2 ▸ rfl]
      wp_call hdealloc_fo (p3, c3.toNat, 1, st2)
      rw [hsp2]
      have hacp : AllocCallPreserved s2 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s2.sp›.trans hsp2
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr2.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  intro st3 s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
  refine seq_evs_st st3 (mid := lsmpl.base 333 + 7176#64)
    (fun st4 sm =>
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool lim st4 sm ∗ Frame)
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc3 ⊢
    change s3.pc = (blkPl_333).base + 7156#64 at hpc3
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7176#64) s3 _ _
    by_cases hc4 : (c4 == 0#64) = true <;>
      simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 7176#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := hsp3 ▸ hfsp_align
      apply sepWP_evs_dealloc c4.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      try simp only [State.setMem_setMem]
      rw [show stackAt (s0.sp - 2400#64) allocHookStack = stackAt s3.sp allocHookStack from hsp3 ▸ rfl]
      wp_call hdealloc_fo (p4, c4.toNat, 1, st3)
      rw [hsp3]
      have hacp : AllocCallPreserved s3 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s3.sp›.trans hsp3
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr3.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s3›.trans htr3.2
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  intro st4 s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx22_4, hx27_4, htr4⟩
  rw [← ls_blockPlacement_base (i := 333)] at hpc4 ⊢
  change s4.pc = (blkPl_333).base + 7176#64 at hpc4
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 7196#64) s4 _ _
  by_cases hc5 : (c5 == 0#64) = true <;>
    simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 7196#64)
    try simp only [State.setMem_setMem]
    dsimp only [P_post]
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl)))
    · wp_done
  · have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := hsp4 ▸ hfsp_align
    apply sepWP_evs_dealloc c5.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    try simp only [State.setMem_setMem]
    rw [show stackAt (s0.sp - 2400#64) allocHookStack = stackAt s4.sp allocHookStack from hsp4 ▸ rfl]
    wp_call hdealloc_fo (p5, c5.toNat, 1, st4)
    rw [hsp4]
    have hacp : AllocCallPreserved s4 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s4.sp›.trans hsp4
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr4.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s4›.trans htr4.2
    dsimp only [P_post]
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      refine Entails.trans (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
        ((((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
          ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
          ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
         A.pool lim (M.stepEvents (rustDeallocEvents c5.toNat 1) st4) _ ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

/-- Budget-threaded placed deallocation of `c2/p2 .. c5/p5` at `+7116 -> +7196` under
`FromPbAllocHooksBudget`. -/
theorem v7_dealloc_4vecs_7116_to_7196_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7116#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7196#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
        vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) :=
  v7_dealloc_4vecs_7116_to_7196_of_placedHooks hA.toPlacedBudget
    s0 s1 out pbA cap_dec c2 p2 c3 p3 c4 p4 c5 p5 st Frame
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx24_1 hx27_1 htr1

/-- Budget-threaded placed deallocation of `c1/p1` at `+7104 -> +7116` when `¬((c1 == 0#64) = true)`
under `FromPbAllocHooksPlacedBudget`. -/
theorem v7_dealloc_c1_7104_to_7116_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 c2 : BitVec 64)
    (st : M.σ) (Frame : SepProp) (hc1 : ¬((c1 == 0#64) = true))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7104#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx1_1 : s1.readReg64 .x1 = c1) (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec) (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA) (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7116#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := hsp1 ▸ hfsp_align
  have hdealloc_fo := v4_sub_ok_dealloc_125316_fo_placed hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  rw [h7552]
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst
  dsimp only [vecCapPtrDealloc, RustCliAllocBudget.repAlloc, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
  simp only [hc1, ↓reduceIte]
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 7104#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 7116#64) s1 _ _
  apply sepWP_evs_dealloc c1.toNat 1
  wp_steps_sync_333 (lsρ spqrRustDeallocSym)
  try simp only [State.setMem_setMem]
  rw [show stackAt (s0.sp - 2400#64) allocHookStack = stackAt s1.sp allocHookStack from hsp1 ▸ rfl]
  wp_call hdealloc_fo (p1, c1.toNat, 1, st)
  rw [hsp1]
  have hacp : AllocCallPreserved s1 sf := by
    simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
  have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s1.sp›.trans hsp1
  have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr1.1
  have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
    ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
  refine entails_pre_st (fun _ hsc => ?_) ?_
  · subst hsc
    refine Entails.trans (Entails.of_eq (show _ =
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (A.pool lim (M.stepEvents (rustDeallocEvents c1.toNat 1) st) _ ∗ Frame) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl))
  · wp_done

/-- Budget-threaded placed deallocation of `c1/p1` at `+7104 -> +7116` under `FromPbAllocHooksBudget`. -/
theorem v7_dealloc_c1_7104_to_7116_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 c2 : BitVec 64)
    (st : M.σ) (Frame : SepProp) (hc1 : ¬((c1 == 0#64) = true))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7104#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx1_1 : s1.readReg64 .x1 = c1) (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec) (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA) (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7116#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) :=
  v7_dealloc_c1_7104_to_7116_of_placedHooks hA.toPlacedBudget
    s0 s1 out pbA cap_dec c1 p1 c2 st Frame hc1
    hsp0_align hpc1 hrun1 hsp1 hx1_1 hx19_1 hx22_1 hx24_1 hx27_1 hx28_1 htr1

/-- Budget-threaded placed cleanup at `+7100 -> +4632` (when `s.sendingCt1 = none`) under
`FromPbAllocHooksPlacedBudget`: deallocates `c1/p1 .. c5/p5` and `optDec` (if `some`), sets
`x28 = 0#64`, and reaches `+4632` under `FreeOnlyEvs`. -/
theorem v7_cleanup_7100_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7100#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx1_1 : s1.readReg64 .x1 = c1) (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec) (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA) (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
        vecCapPtrDealloc A.repAlloc c5 p5 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          memRegion (pbA + 184#64) 40 ∗ A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  let P_post : M.σ → State → SepProp := fun stf sm =>
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
      memRegion (pbA + 184#64) 40 ∗ A.pool lim stf sm ∗ Frame
  refine seq_evs_st st (mid := lsmpl.base 333 + 7116#64)
    (fun st1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool lim st1 sm ∗
      (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
       vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
       vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame))
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x24 = c2 ∧
      sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) ?_ ?_
  · by_cases hc1 : (c1 == 0#64) = true
    · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      simp only [hc1, ↓reduceIte, emp_sepConj, sepConj_emp]
      rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 7100#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 7116#64) s1 _ _
      apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 7116#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · refine seq_clean_st (mid := lsmpl.base 333 + 7104#64)
        (P_mid := fun sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          vecCapPtrDealloc A.repAlloc c1 p1 ∗ A.pool lim st sm ∗
          (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
           vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
           vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame))
        (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x1 = c1 ∧
          sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x24 = c2 ∧ sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = p1 ∧ TraceCalleeSaved sm s0) ?_ ?_
      · rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
        change s1.pc = (blkPl_333).base + 7100#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7104#64) s1 _ _
        wp_steps_sync_333 ((blkPl_333).base + 7104#64)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx1_2, hx19_2, hx22_2, hx24_2, hx27_2, hx28_2, htr2⟩
        exact v7_dealloc_c1_7104_to_7116_of_placedHooks hA s0 s2 out pbA cap_dec c1 p1 c2 st _
          hc1 hsp0_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx22_2 hx24_2 hx27_2 hx28_2 htr2
  · intro st1 s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx24_2, hx27_2, htr2⟩
    refine seq_evs_st st1 (mid := lsmpl.base 333 + 7196#64)
      (fun st2 sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        A.pool lim st2 sm ∗
        ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame))
      P_post
      (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) ?_ ?_
    · refine SepWP.weaken_pre ?_
        (v7_dealloc_4vecs_7116_to_7196_of_placedHooks hA s0 s2 out pbA cap_dec c2 p2 c3 p3 c4 p4 c5 p5 st1
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame)
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx24_2 hx27_2 htr2)
      exact Entails.of_eq (by sep_ac_rfl)
    · intro st2 s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
      have h7196 := v7_cleanup_7196_of_placedHooks hA s0 s3 out pbA cap_dec optDec st2
        (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗ Frame)
        hcap_dec hsp0_align hpc3 hrun3 hsp3 hx19_3 hx22_3 hx27_3 htr3
      refine SepWP.weaken_pre ?_
        (SepWP.mono h7196 fun _ _ _ _ ⟨evs, hevs, hPm, hq⟩ =>
          ⟨evs, hevs, Entails.trans hPm (by dsimp only [P_post]; exact Entails.of_eq (by sep_ac_rfl)), hq⟩)
      exact Entails.of_eq (by sep_ac_rfl)

/-- Budget-threaded placed cleanup at `+7100 -> +4632` under `FromPbAllocHooksBudget`. -/
theorem v7_cleanup_7100_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7100#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx1_1 : s1.readReg64 .x1 = c1) (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec) (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA) (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
        vecCapPtrDealloc A.repAlloc c5 p5 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          memRegion (pbA + 184#64) 40 ∗ A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) :=
  v7_cleanup_7100_of_placedHooks hA.toPlacedBudget
    s0 s1 out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 optDec st Frame
    hcap_dec hsp0_align hpc1 hrun1 hsp1 hx1_1 hx19_1 hx22_1 hx24_1 hx27_1 hx28_1 htr1

/-- Budget-threaded placed cleanup at `+3732 -> +4632` (when `<PolyEncoder>::from_pb = Err`)
under `FromPbAllocHooksPlacedBudget`: loads `c1` from `[sp, #0x18]`, deallocates `c1/p1 .. c5/p5`
and `optDec` (if `some`), sets `x28 = 0#64`, and reaches `+4632` under `FreeOnlyEvs`. -/
theorem v7_cleanup_3732_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3732#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2) (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
        vecCapPtrDealloc A.repAlloc c5 p5 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          memRegion (pbA + 184#64) 40 ∗ A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have h24 : (s0.sp - 2400#64) + 24#64 = s0.sp - 2376#64 := by bv_omega
  let P_post : M.σ → State → SepProp := fun stf sm =>
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
      v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
      memRegion (pbA + 184#64) 40 ∗ A.pool lim stf sm ∗ Frame
  refine seq_evs_st st (mid := lsmpl.base 333 + 7116#64)
    (fun st1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool lim st1 sm ∗
      (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
       vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
       vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
       ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame)))
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x24 = c2 ∧
      sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) ?_ ?_
  · by_cases hc1 : (c1 == 0#64) = true
    · rw [h24]
      dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      simp only [hc1, Bool.true_eq_false, ↓reduceIte, emp_sepConj, sepConj_emp]
      rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 3732#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 7116#64) s1 _ _
      apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 7116#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · refine seq_clean_st (mid := lsmpl.base 333 + 7104#64)
        (P_mid := fun sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          vecCapPtrDealloc A.repAlloc c1 p1 ∗ A.pool lim st sm ∗
          (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
           vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
           vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
           ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame)))
        (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x1 = c1 ∧
          sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x24 = c2 ∧ sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = p1 ∧ TraceCalleeSaved sm s0) ?_ ?_
      · rw [h24]
        rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
        change s1.pc = (blkPl_333).base + 3732#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7104#64) s1 _ _
        wp_steps_sync_333 ((blkPl_333).base + 7104#64)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx1_2, hx19_2, hx22_2, hx24_2, hx27_2, hx28_2, htr2⟩
        exact v7_dealloc_c1_7104_to_7116_of_placedHooks hA s0 s2 out pbA cap_dec c1 p1 c2 st _
          hc1 hsp0_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx22_2 hx24_2 hx27_2 hx28_2 htr2
  · intro st1 s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx24_2, hx27_2, htr2⟩
    refine seq_evs_st st1 (mid := lsmpl.base 333 + 7196#64)
      (fun st2 sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        A.pool lim st2 sm ∗
        ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
         ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame)))
      P_post
      (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) ?_ ?_
    · refine SepWP.weaken_pre ?_
        (v7_dealloc_4vecs_7116_to_7196_of_placedHooks hA s0 s2 out pbA cap_dec c2 p2 c3 p3 c4 p4 c5 p5 st1
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
           ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame))
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx24_2 hx27_2 htr2)
      exact Entails.of_eq (by sep_ac_rfl)
    · intro st2 s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
      have h7196 := v7_cleanup_7196_of_placedHooks hA s0 s3 out pbA cap_dec optDec st2
        (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
         ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame))
        hcap_dec hsp0_align hpc3 hrun3 hsp3 hx19_3 hx22_3 hx27_3 htr3
      refine SepWP.weaken_pre ?_
        (SepWP.mono h7196 fun _ _ _ _ ⟨evs, hevs, hPm, hq⟩ =>
          ⟨evs, hevs, Entails.trans hPm (by dsimp only [P_post]; exact Entails.of_eq (by sep_ac_rfl)), hq⟩)
      exact Entails.of_eq (by sep_ac_rfl)

/-- Budget-threaded placed cleanup at `+3732 -> +4632` under `FromPbAllocHooksBudget`. -/
theorem v7_cleanup_3732_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3732#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2) (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
        vecCapPtrDealloc A.repAlloc c5 p5 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          memRegion (pbA + 184#64) 40 ∗ A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) :=
  v7_cleanup_3732_of_placedHooks hA.toPlacedBudget
    s0 s1 out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 optDec st Frame
    hcap_dec hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx24_1 hx27_1 hx28_1 htr1

/-! ## 2. Cleanup at `+10556..+10672 -> +11112 -> +4632` (`s.receivingEk = none`) -/

theorem v7_drop_poly16_pre_pool (A : RustAlloc) (fsp : BitVec 64) (enc : PolyEncoder)
    (Pool Frame : SepProp) :
    stackAt fsp encoderFromPbStack ∗ polyEncoderAt A (fsp + 1392#64) enc ∗ Pool ∗ Frame ⊢
    ∃∗ tag : BitVec 64, ∃∗ vecs : List (List GF16),
      ⌜vecs.length = NUM_POLYS⌝ ∗
      ((stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
       ((fsp + 1392#64) ↦₆₄ tag) ∗ vecGF16ListOf A ((fsp + 1392#64) + 8#64) vecs ∗
       memRegion ((fsp + 1392#64) + 392#64) 8 ∗ Pool ∗ Frame) := by
  refine Entails.trans
    (sepConj_mono
      (v7_stackAt_encoderFromPbStack_to_dropStack32 fsp)
      (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A (fsp + 1392#64) enc))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro tag
  apply Entails.sepExists_elim; intro vecs
  exact Entails.sepExists_right tag (Entails.sepExists_right vecs (Entails.of_eq (by sep_ac_rfl)))

/-- Budget-threaded placed step `+10556 -> +10568`: drops `[Poly; 16]` at
`(s0.sp - 2400#64) + 1400#64` via Block `265` under `FreeOnlyEvs` and combines with the tag and tail
to leave `memRegion ((s0.sp - 2400#64) + 1392#64) 400`. -/
theorem v7_drop_poly16_10556_to_10568_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out c2 : BitVec 64)
    (enc : PolyEncoder) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10556#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10568#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x24 = c2 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  refine SepWP.weaken_pre
    (v7_drop_poly16_pre_pool A.repAlloc (s0.sp - 2400#64) enc (A.pool lim st s1) Frame) ?_
  apply ProofLib.SepWP.exists_left; intro tag
  apply ProofLib.SepWP.exists_left; intro vecs
  apply ProofLib.SepWP.pure_elim; intro hvecs_len
  have h1392 : (s0.sp - 2400#64) + 1392#64 = s0.sp - 1008#64 := by bv_omega
  have h1400 : (s0.sp - 1008#64) + 8#64 = s0.sp - 1000#64 := by bv_omega
  have h1784 : (s0.sp - 1008#64) + 392#64 = s0.sp - 616#64 := by bv_omega
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  rw [h1392, h1400, h1784, h7552]
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 265)
    (P_mid := fun sm =>
      vecGF16ListOf A.repAlloc (s0.sp - 1000#64) vecs ∗
      A.pool lim st sm ∗
      stackAt (s0.sp - 2400#64) dropStack32 ∗
      (memRegion (s0.sp - 7552#64) 1024 ∗
       ((s0.sp - 1008#64) ↦₆₄ tag) ∗
       memRegion (s0.sp - 616#64) 8 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x0 = s0.sp - 1000#64 ∧
      sm.readReg64 .lr = (blkPl_333).base + 10568#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x24 = c2 ∧
      TraceCalleeSaved sm s0) ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc1
    change s1.pc = (blkPl_333).base + 10556#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 265) s1 _ _
    wp_steps_sync_333 (lsmpl.base 265)
    try simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hlr_2, hx19_2, hx24_2, htr2⟩
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
    have hdrop := v7_sub_ok_drop_poly16_mem_placed hA hcl2
    simp only [withMemEq, dropGluePoly16Spec, dropGluePoly16Stack] at hdrop
    dsimp only [polyArrayBytes, BitVec.ofNat_eq_ofNat] at hdrop ⊢
    rw [← ls_blockPlacement_base (i := 333)]
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10568#64) s2 _ _
    rw [show stackAt (s0.sp - 2400#64) dropStack32 = stackAt s2.sp dropStack32 from hsp2 ▸ rfl]
    wp_call hdrop ((⟨s0.sp - 1000#64, vecs⟩ : DropGluePoly16Ghost), st)
    rw [hsp2]
    rw [hlr_2] at *
    have hevs_w : FreeOnlyEvs w := ‹_›
    have hacp_w : AllocCallPreserved s2 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s2.sp›.trans hsp2
    have htr_sf : sf.trace = s0.trace := hacp_w.2.1.trans htr2.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
    apply sepWP_with_evs w hevs_w
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      have hst := v7_stackAt_dropStack32_to_encoderFromPbStack (s0.sp - 2400#64)
      have hjoin := v7_polyEncoder_1392_join (s0.sp - 2400#64) tag
      have h1400' : (s0.sp - 2400#64) + 1400#64 = s0.sp - 1000#64 := by bv_omega
      have h1784' : (s0.sp - 2400#64) + 1784#64 = s0.sp - 616#64 := by bv_omega
      rw [h7552] at hst
      rw [h1392, h1400', h1784'] at hjoin
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
          ((((s0.sp - 1008#64) ↦₆₄ tag) ∗
            memRegion (s0.sp - 1000#64) 384 ∗
            memRegion (s0.sp - 616#64) 8) ∗
           (A.pool lim (M.stepEvents w st) _ ∗ Frame)) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hst (sepConj_mono_left hjoin)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

/-- Budget-threaded placed deallocation of `c1/p1` at `+10568 -> +10588` under
`FromPbAllocHooksPlacedBudget`. -/
theorem v7_dealloc_c1_10568_to_10588_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (out c1 p1 c2 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10568#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10588#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x24 = c2 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc_fo := v4_sub_ok_dealloc_125316_fo_placed hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
  have h24 : (s0.sp - 2400#64) + 24#64 = s0.sp - 2376#64 := by bv_omega
  rw [h7552, h200, h24]
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst
  dsimp only [vecCapPtrDealloc, RustCliAllocBudget.repAlloc, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
  rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
  change s1.pc = (blkPl_333).base + 10568#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 10588#64) s1 _ _
  by_cases hc1 : (c1 == 0#64) = true <;>
    simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 10588#64)
    try simp only [State.setMem_setMem]
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl)))
    · wp_done
  · have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := hsp1 ▸ hfsp_align
    apply sepWP_evs_dealloc c1.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    try simp only [State.setMem_setMem]
    rw [show stackAt (s0.sp - 2400#64) allocHookStack = stackAt s1.sp allocHookStack from hsp1 ▸ rfl]
    wp_call hdealloc_fo (p1, c1.toNat, 1, st)
    rw [hsp1]
    have hacp : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s1.sp›.trans hsp1
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr1.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      refine Entails.trans (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
        (((s0.sp - 2200#64) ↦₆₄ p1) ∗ ((s0.sp - 2376#64) ↦₆₄ c1) ∗
         A.pool lim (M.stepEvents (rustDeallocEvents c1.toNat 1) st) _ ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

/-- Budget-threaded placed deallocation of `c1/p1` at `+10568 -> +10588` under
`FromPbAllocHooksBudget`. -/
theorem v7_dealloc_c1_10568_to_10588_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out c1 p1 c2 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10568#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10588#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x24 = c2 ∧
        TraceCalleeSaved sm s0) :=
  v7_dealloc_c1_10568_to_10588_of_placedHooks hA.toPlacedBudget
    s0 s1 out c1 p1 c2 st Frame hsp0_align hpc1 hrun1 hsp1 hx19_1 hx24_1 htr1

private theorem v7_dealloc_c2c3_10588_to_10628_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (out c2 p2 c3 p3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10588#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10628#64) s1
      ((stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
        (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3)) ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
          (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc_fo := v4_sub_ok_dealloc_125316_fo_placed hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [vecCapPtrDealloc, RustCliAllocBudget.repAlloc, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
  let P_post : M.σ → State → SepProp := fun stf sm =>
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3)) ∗
      A.pool lim stf sm ∗ Frame
  refine seq_evs_st st (mid := lsmpl.base 333 + 10608#64)
    (fun st1 sm =>
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3)) ∗
      (if (c3 == 0#64) = true then emp else A.live p3 c3.toNat 1 ∗ memRegion p3 c3.toNat) ∗
      A.pool lim st1 sm ∗ Frame)
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0) ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 10588#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10608#64) s1 _ _
    by_cases hc2 : (c2 == 0#64) = true <;>
      simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 10608#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := hsp1 ▸ hfsp_align
      apply sepWP_evs_dealloc c2.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      try simp only [State.setMem_setMem]
      rw [show stackAt (s0.sp - 2400#64) allocHookStack = stackAt s1.sp allocHookStack from hsp1 ▸ rfl]
      wp_call hdealloc_fo (p2, c2.toNat, 1, st)
      rw [hsp1]
      have hacp : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s1.sp›.trans hsp1
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr1.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  intro st2 s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
  rw [← ls_blockPlacement_base (i := 333)] at hpc2 ⊢
  change s2.pc = (blkPl_333).base + 10608#64 at hpc2
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 10628#64) s2 _ _
  by_cases hc3 : (c3 == 0#64) = true <;>
    simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 10628#64)
    try simp only [State.setMem_setMem]
    dsimp only [P_post]
    refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  · have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
    apply sepWP_evs_dealloc c3.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    try simp only [State.setMem_setMem]
    rw [show stackAt (s0.sp - 2400#64) allocHookStack = stackAt s2.sp allocHookStack from hsp2 ▸ rfl]
    wp_call hdealloc_fo (p3, c3.toNat, 1, st2)
    rw [hsp2]
    have hacp : AllocCallPreserved s2 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s2.sp›.trans hsp2
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr2.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
    dsimp only [P_post]
    refine align_pre_st (by sep_ac_rfl) ?_; wp_done

private theorem v7_dealloc_c4c5_10628_to_11112_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s3 : State) (out c4 p4 c5 p5 : BitVec 64)
    (st3 : M.σ) (Frame : SepProp)
    (hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true)
    (h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64)
    (hpc3 : s3.pc = lsmpl.base 333 + 10628#64)
    (hrun3 : s3.status = .Running) (hsp3 : s3.sp = s0.sp - 2400#64)
    (hx19_3 : s3.readReg64 .x19 = out)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11112#64) s3
      ((stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
        (((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗
         ((s0.sp - 1040#64) ↦₆₄ c5) ∗ ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
        vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
        A.pool lim st3 s3 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗
           ((s0.sp - 1040#64) ↦₆₄ c5) ∗ ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
          A.pool lim (M.stepEvents evs st3) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc_fo := v4_sub_ok_dealloc_125316_fo_placed hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst
  dsimp only [vecCapPtrDealloc, RustCliAllocBudget.repAlloc, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc3 ⊢
  let P_post : M.σ → State → SepProp := fun stf sm =>
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗
       ((s0.sp - 1040#64) ↦₆₄ c5) ∗ ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      A.pool lim stf sm ∗ Frame
  refine seq_evs_st st3 (mid := lsmpl.base 333 + 10648#64)
    (fun st4 sm =>
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗
       ((s0.sp - 1040#64) ↦₆₄ c5) ∗ ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool lim st4 sm ∗ Frame)
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0) ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc3 ⊢
    change s3.pc = (blkPl_333).base + 10628#64 at hpc3
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10648#64) s3 _ _
    by_cases hc4 : (c4 == 0#64) = true <;>
      simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 10648#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := hsp3 ▸ hfsp_align
      apply sepWP_evs_dealloc c4.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      try simp only [State.setMem_setMem]
      rw [show stackAt (s0.sp - 2400#64) allocHookStack = stackAt s3.sp allocHookStack from hsp3 ▸ rfl]
      wp_call hdealloc_fo (p4, c4.toNat, 1, st3)
      rw [hsp3]
      have hacp : AllocCallPreserved s3 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s3.sp›.trans hsp3
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr3.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s3›.trans htr3.2
      refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  intro st4 s4 hpc4 hrun4 ⟨hsp4, hx19_4, htr4⟩
  rw [← ls_blockPlacement_base (i := 333)] at hpc4 ⊢
  change s4.pc = (blkPl_333).base + 10648#64 at hpc4
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 11112#64) s4 _ _
  by_cases hc5 : (c5 == 0#64) = true <;>
    simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 11112#64)
    try simp only [State.setMem_setMem]
    dsimp only [P_post]
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl)))
    · wp_done
  · have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := hsp4 ▸ hfsp_align
    apply sepWP_evs_dealloc c5.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    try simp only [State.setMem_setMem]
    rw [show stackAt (s0.sp - 2400#64) allocHookStack = stackAt s4.sp allocHookStack from hsp4 ▸ rfl]
    wp_call hdealloc_fo (p5, c5.toNat, 1, st4)
    rw [hsp4]
    have hacp : AllocCallPreserved s4 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s4.sp›.trans hsp4
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr4.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s4›.trans htr4.2
    wp_steps_sync_333 ((blkPl_333).base + 11112#64)
    try simp only [State.setMem_setMem]
    dsimp only [P_post]
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      refine Entails.trans (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
        ((((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗
          ((s0.sp - 1040#64) ↦₆₄ c5) ∗ ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
         A.pool lim (M.stepEvents (rustDeallocEvents c5.toNat 1) st4) _ ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

/-- Budget-threaded placed deallocation of the 4 `Vec<u8>` buffers `c2/p2 .. c5/p5` at
`+10588 -> +11112` under `FromPbAllocHooksPlacedBudget`. -/
theorem v7_dealloc_4vecs_10588_to_11112_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (out c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10588#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11112#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
        vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  have h1296 : (s0.sp - 2400#64) + 1296#64 = s0.sp - 1104#64 := by bv_omega
  have h1312 : (s0.sp - 2400#64) + 1312#64 = s0.sp - 1088#64 := by bv_omega
  have h1320 : (s0.sp - 2400#64) + 1320#64 = s0.sp - 1080#64 := by bv_omega
  have h1336 : (s0.sp - 2400#64) + 1336#64 = s0.sp - 1064#64 := by bv_omega
  have h1344 : (s0.sp - 2400#64) + 1344#64 = s0.sp - 1056#64 := by bv_omega
  have h1360 : (s0.sp - 2400#64) + 1360#64 = s0.sp - 1040#64 := by bv_omega
  have h1368 : (s0.sp - 2400#64) + 1368#64 = s0.sp - 1032#64 := by bv_omega
  unfold v7_ct1SentSpillCells CryptoVerification.SpqrV1.States.FromPb.v7_ct1SentSpillCells
  rw [h7552, h1296, h1312, h1320, h1336, h1344, h1360, h1368]
  let P_post : M.σ → State → SepProp := fun stf sm =>
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      A.pool lim stf sm ∗ Frame
  refine seq_evs_st st (mid := lsmpl.base 333 + 10628#64)
    (fun st2 sm =>
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3)) ∗
      A.pool lim st2 sm ∗
      ((((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗
        ((s0.sp - 1040#64) ↦₆₄ c5) ∗ ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
       vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗ Frame))
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0) ?_ ?_
  · refine SepWP.weaken_pre ?_
      (v7_dealloc_c2c3_10588_to_10628_of_placedHooks hA s0 s1 out c2 p2 c3 p3 st
        ((((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗
          ((s0.sp - 1040#64) ↦₆₄ c5) ∗ ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
         vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗ Frame)
        hfsp_align hpc1 hrun1 hsp1 hx19_1 hx24_1 htr1)
    exact Entails.of_eq (by sep_ac_rfl)
  · intro st2 s3 hpc3 hrun3 ⟨hsp3, hx19_3, htr3⟩
    have hc4c5 := v7_dealloc_c4c5_10628_to_11112_of_placedHooks hA s0 s3 out c4 p4 c5 p5 st2
      ((((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3)) ∗ Frame)
      hfsp_align h7552 hpc3 hrun3 hsp3 hx19_3 htr3
    refine SepWP.weaken_pre ?_
      (SepWP.mono hc4c5 fun _ _ _ _ ⟨evs, hevs, hPm, hq⟩ =>
        ⟨evs, hevs, Entails.trans hPm (by dsimp only [P_post]; exact Entails.of_eq (by sep_ac_rfl)), hq⟩)
    exact Entails.of_eq (by sep_ac_rfl)

/-- Budget-threaded placed deallocation of `c2/p2 .. c5/p5` at `+10588 -> +11112` under
`FromPbAllocHooksBudget`. -/
theorem v7_dealloc_4vecs_10588_to_11112_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10588#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11112#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
        vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) :=
  v7_dealloc_4vecs_10588_to_11112_of_placedHooks hA.toPlacedBudget
    s0 s1 out c2 p2 c3 p3 c4 p4 c5 p5 st Frame
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx24_1 htr1

/-- Budget-threaded placed cleanup at `+10556 -> +4632` (when `s.receivingEk = none`):
drops `enc` at `fsp + 1392..1792`, deallocates `c1/p1 .. c5/p5`, sets `x28 = 0#64` at `+11112`,
and branches to `+4632` under `FreeOnlyEvs`. -/
theorem v7_cleanup_10556_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (enc : PolyEncoder) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10556#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
        vecCapPtrDealloc A.repAlloc c5 p5 ∗ A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  let P_post : M.σ → State → SepProp := fun stf sm =>
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
      v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
      A.pool lim stf sm ∗ Frame
  refine seq_evs_st st (mid := lsmpl.base 333 + 10568#64)
    (fun st1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ A.pool lim st1 sm ∗
      ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
       vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
       vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
       vecCapPtrDealloc A.repAlloc c5 p5 ∗ Frame))
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x24 = c2 ∧ TraceCalleeSaved sm s0) ?_ ?_
  · refine SepWP.weaken_pre ?_
      (v7_drop_poly16_10556_to_10568_placed hA s0 s1 out c2 enc st
        ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
         v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
         vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
         vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
         vecCapPtrDealloc A.repAlloc c5 p5 ∗ Frame)
        hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx24_1 htr1)
    exact Entails.of_eq (by sep_ac_rfl)
  · intro st1 s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx24_2, htr2⟩
    refine seq_evs_st st1 (mid := lsmpl.base 333 + 10588#64)
      (fun st2 sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        A.pool lim st2 sm ∗
        (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
         vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
         vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
         memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame))
      P_post
      (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x24 = c2 ∧ TraceCalleeSaved sm s0) ?_ ?_
    · refine SepWP.weaken_pre ?_
        (v7_dealloc_c1_10568_to_10588_placed hA s0 s2 out c1 p1 c2 st1
          (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
           vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
           vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
           memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame)
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx24_2 htr2)
      exact Entails.of_eq (by sep_ac_rfl)
    · intro st2 s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx24_3, htr3⟩
      refine seq_clean_evs
        (mid := lsmpl.base 333 + 11112#64)
        (P_evs := fun evs3 sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool lim (M.stepEvents evs3 st2) sm ∗
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
           memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame))
        (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0) ?_ ?_
      · refine SepWP.weaken_pre ?_
          (v7_dealloc_4vecs_10588_to_11112_placed hA s0 s3 out c2 p2 c3 p3 c4 p4 c5 p5 st2
            ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
             memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame)
            hsp0_align hpc3 hrun3 hsp3 hx19_3 hx24_3 htr3)
        exact Entails.of_eq (by sep_ac_rfl)
      · intro evs3 s4 hevs3 hpc4 hrun4 ⟨hsp4, hx19_4, htr4⟩
        have h11112 := v7_cleanup_11112_placed_budget A lim (M.stepEvents evs3 st2) (ext := ext)
          s0 s4 out
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
           v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗ Frame)
          hpc4 hrun4 hsp4 hx19_4 htr4
        have hpre_eq :
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
              v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
              A.pool lim (M.stepEvents evs3 st2) s4 ∗
              ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
               memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame) =
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
              memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
              (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
              v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗ Frame) ∗
              A.pool lim (M.stepEvents evs3 st2) s4 := by
          sep_ac_rfl
        exact SepWP.weaken_pre (Entails.of_eq hpre_eq)
          (SepWP.mono h11112 fun _ _ _ _ ⟨hPm, _, hrest⟩ =>
            ⟨evs3, hevs3, Entails.trans hPm (by dsimp only [P_post]; exact Entails.of_eq (by sep_ac_rfl)), hrest⟩)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7cPlacedBudget
