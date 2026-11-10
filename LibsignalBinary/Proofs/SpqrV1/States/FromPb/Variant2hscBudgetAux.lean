/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueBudget
public meta import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueBudget -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsc
public import LibsignalBinary.Heap.IfaceBudgetBase
public meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
meta import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Fixed-Offset Budget Error Exits for `Variant2hsc`

Error exits (`+9224`, `+9228`) and `FreeOnlyEvs` inline `ProtoPolynomialDecoder` deallocation
(`+4428..+4512 -> +9228`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecU8)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialDecoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Drop (
  add_24_add_8 cap_mul_24 chunkedStatesSize cons_len_mul header_cells_entails_memRegion_24
  ofNat_add_one_beq_one_false_24 ofNat_beq_zero_false_24 ofNat_succ_eq_add_one
  sep_pull_body sep_push_body sep_rejoin_loop
  tail_len_mul_lt vecCapPtrDealloc vecU8_entails_capPtr_dealloc
)
open CryptoVerification.SpqrV1.Poly (boolByte)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (align_pre encoderFromPbStack)
open CryptoVerification.SpqrV1.Unchunked (
  extractLsb'_0_64_append extractLsb'_64_64_append
)
open CryptoVerification.SpqrV1.Layout.Stubs (stubOff_rust_dealloc)
open CryptoVerification.SpqrV1.States.FromPb (
  TraceCalleeSaved collapse_step collapse_step0 collapse_top
  memRegion_out_928_split_32 out_8_32_entails_err_tail resultChunkedStatesAt
  spqrErrorByte statesFromPbName statesFromPbSavedCells statesFromPbStack
  statesFromPb_fnOff v2hsc_Saved4436Preserved v2hsc_bfm_loByte_eq
  v2hsc_bv_add_add_lit v2hsc_optProtoPolyDecoderHeap v2hsc_optProtoPolyDecoderWordsAt
  v2hsc_ptsCap_add_one_ne_zero v2hsc_stackAt_allocHook_to_encoderFromPbStack
  v2hsc_stackAt_encoderFromPbStack_to_allocHook
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpecBase rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueBudget (states_from_pb_epilogue_60)
open scoped CryptoVerification.CodeLayout
open scoped LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueBudget

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append v2hsc_bv_add_add_lit
attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff stubOff_rust_dealloc TraceCalleeSaved

/-! ## Shared Budget Combinators -/

theorem fnAddr_rebase_hooks_eq (P : Program) (b : BitVec 64)
    (h1 h2 : String → Option (State → State)) (name : String) :
    (P.rebase b h1).fnAddr name = (P.rebase b h2).fnAddr name := by
  unfold Program.fnAddr Program.fnOff; rfl

def deallocFreeOnlySpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpecBase M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

theorem subroutine_ok_deallocFreeOnly {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpecBase, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

theorem v2hsc_sub_ok_dealloc_125316_fo
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc"))
      (deallocFreeOnlySpec M A lim) :=
  subroutine_ok_deallocFreeOnly
    (hA.dealloc_ok_at statesFromPbName
      (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")))

theorem allocCallPreserved_of_step {s s' sf : State}
    (h2 : AllocCallPreserved s' sf) (h1 : AllocCallPreserved s s') : AllocCallPreserved s sf :=
  h1.trans h2

theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

theorem seq_clean_st {prog : Program} {mid target : BitVec 64} {s : State}
    {Pre : SepProp} {P_mid : State → SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s Pre (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

theorem seq_clean_evs {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs, hevs, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 evs sm hevs hpc hrun hQ)

theorem sepWP_evs_nil {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs [] sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨[], FreeOnlyEvs.nil, hp, hq⟩

theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ =>
    ⟨rustDeallocEvents sz al, FreeOnlyEvs.singleton al sz, hp, hq⟩

theorem strengthen_entails_evs {M : AllocCostModel}
    {prog : Program} {target : BitVec 64} {s : State} {st : M.σ}
    {Pre : SepProp} {P1 P2 : M.σ → State → SepProp} {Q : State → Prop}
    (hent : ∀ st' sf, P1 st' sf ⊢ P2 st' sf)
    (h : SepWP prog target s Pre (fun sf Pf =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pf ⊢ P1 (M.stepEvents evs st) sf) ∧ Q sf)) :
    SepWP prog target s Pre (fun sf Pf =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pf ⊢ P2 (M.stepEvents evs st) sf) ∧ Q sf) :=
  SepWP.mono h fun sf _Pf _ _ ⟨evs, hevs, hp, hq⟩ =>
    ⟨evs, hevs, Entails.trans hp (hent _ sf), hq⟩

/-! ## Error Exit Tails (`+9228 -> s0.x30` and `+9224 -> s0.x30`) -/

theorem v2hsc_err_exit_9228
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : CryptoVerification.LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : (s1.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        AllocCallPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases htr1 with ⟨htr1, hvregs1⟩
  rw [memRegion_out_928_split_32 out]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v24
  apply ProofLib.SepWP.exists_left; intro v16
  apply ProofLib.SepWP.exists_left; intro v8
  apply ProofLib.SepWP.exists_left; intro v0
  refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 60#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      (out ↦₆₄ v0) ∗
      ((out + 8#64) ↦₈ spqrErrorByte err) ∗
      memRegion (out + 9#64) 919 ∗
      Rest)
    (Q := fun sm =>
      AllocCallPreserved s1 sm ∧
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x8 = noneCap ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range_b b trapHooks 9228 20
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_vm_steps {
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      refine ⟨by simp [wp_norm, arm64_norm], ?_, by simp [wp_norm, arm64_norm, noneCap, *]⟩
      have hbfm : ((s1.readReg64 .x23 &&& 255#64 |||
          (s1.readReg64 .x26 &&& 72057594037927935#64) <<< 8).extractLsb' 0 8) =
          spqrErrorByte err := by
        rw [v2hsc_bfm_loByte_eq, hx23_1]
      have htail := out_8_32_entails_err_tail out
        (s1.readReg64 .x23 &&& 255#64 ||| (s1.readReg64 .x26 &&& 72057594037927935#64) <<< 8)
        (s1.readReg64 .x25) (s1.readReg64 .x21)
      rw [hbfm] at htail
      refine Entails.trans (Entails.of_eq (show _ =
        (((out + 8#64) ↦₆₄ (s1.readReg64 .x23 &&& 255#64 |||
            (s1.readReg64 .x26 &&& 72057594037927935#64) <<< 8)) ∗
         ((out + 16#64) ↦₆₄ s1.readReg64 .x25) ∗
         ((out + 24#64) ↦₆₄ s1.readReg64 .x21) ∗
         memRegion (out + 32#64) 896) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 2304 ∗
         statesFromPbSavedCells s0 ∗
         (out ↦₆₄ v0) ∗
         Rest) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by sep_ac_rfl))
    }
  · intro s2 hpc2 hrun2 hvm2 ⟨hacp2, hsp2, hx8_2, hx19_2, htr2⟩
    exact SepWP.mono
      (states_from_pb_epilogue_60 s0 s2 out err v0 Rest hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2)
      fun sf _Pf _ _ ⟨hPf, hvm_f, hacp_f, hsp_f, hcc_f, htr_f⟩ =>
        ⟨hPf, hvm2.trans hvm_f, hacp2.trans hacp_f, hsp_f, hcc_f, htr_f⟩

theorem v2hsc_err_exit_9224
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : CryptoVerification.LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9224#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : (s1.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        AllocCallPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases htr1 with ⟨htr1, hvregs1⟩
  have hsp_split : memRegion (s0.sp - 2400#64) 2304 =
      memRegion (s0.sp - 2400#64) 232 ∗
      (∃∗ w232 : BitVec 64, ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232)) ∗
      memRegion (s0.sp - 2400#64 + 240#64) 2064 := by
    rw [ProofLib.memRegion_split (s0.sp - 2400#64) 232 2072 (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 2400#64 + 232#64) (n := 8) (k := 2064)
          (b' := s0.sp - 2400#64 + 240#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (s0.sp - 2400#64 + 232#64)]
  rw [hsp_split]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w232
  have hm2304 : memRegion (s0.sp - 2400#64) 232 ∗
      ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
      memRegion (s0.sp - 2400#64 + 240#64) 2064 ⊢
      memRegion (s0.sp - 2400#64) 2304 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (ProofLib.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      Rest)
    (Q := fun sm =>
      AllocCallPreserved s1 sm ∧
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range_b b trapHooks 9224 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_vm_steps {
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      refine ⟨by simp [wp_norm, arm64_norm], ?_, by simp [wp_norm, arm64_norm, *]⟩
      simp only [wp_norm, arm64_norm] at hm2304 ⊢
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion (s0.sp - 2400#64) 232 ∗
         ((s0.sp - 2168#64) ↦₆₄ w232) ∗
         memRegion (s0.sp - 2160#64) 2064) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hm2304) (Entails.of_eq (by sep_ac_rfl))
    }
  · intro s2 hpc2 hrun2 hvm2 ⟨hacp2, hsp2, hx19_2, hx23_2, htr2⟩
    exact SepWP.mono
      (v2hsc_err_exit_9228 s0 s2 out err Rest hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 htr2)
      fun sf _Pf _ _ ⟨hPf, hvm_f, hacp_f, hsp_f, hcc_f, htr_f⟩ =>
        ⟨hPf, hvm2.trans hvm_f, hacp2.trans hacp_f, hsp_f, hcc_f, htr_f⟩

/-! ## Shared `ProtoPolynomialDecoder` Deallocation (`+4428..+4512 -> +9228`) -/

theorem v2hsc_proto_decoder_dealloc_body_4460
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4460#64 →
      s.status = .Running →
      v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x24 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4448#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
          sm.readReg64 .x21 = cnt ∧
          sm.readReg64 .x24 = cur + 8#64 ∧
          AllocCallPreserved s sm) := by
  have hdealloc := v2hsc_sub_ok_dealloc_125316_fo hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 4460 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro cur cnt bs st s Frame hpc hrun hpres hx21 hx24
  rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htr, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro vptr
  have hpost24 (Pool : SepProp) :
      ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
        (Pool ∗ stackAt fsp allocHookStack ∗ Frame) ⊢
      memRegion cur 24 ∗ Pool ∗ stackAt fsp allocHookStack ∗ Frame := by
    refine Entails.trans (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  by_cases hcap : (cap == 0#64) = true
  · simp only [hcap, ↓reduceIte, sepConj_emp]
    apply sepWP_evs_nil
    simp only [AllocCostModel.stepEvents_nil]
    wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨?_, by simp [v2hsc_Saved4436Preserved, wp_norm, arm64_norm, *]⟩
    simp only [wp_norm, arm64_norm]
    exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hpost24 (A.pool lim st s))
  · have hcap_f : (cap == 0#64) = false := Bool.eq_false_iff.mpr hcap
    simp only [hcap_f, Bool.false_eq_true, ↓reduceIte]
    apply sepWP_evs_dealloc cap.toNat 1
    wp_steps
    wp_apply
    have hacp_all : AllocCallPreserved s sf :=
      allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
    have ⟨_, _, _, _, _, _, _⟩ := hacp_all
    wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
    have hsp_sf' : sf.sp = fsp := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp])
    refine ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm]
      rw [← hsp_sf, hsp_sf']
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (hpost24 (A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sf))
    · simp [v2hsc_Saved4436Preserved, wp_norm, arm64_norm, hsp_sf', *]

theorem v2hsc_proto_decoder_dealloc_loop_4460
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4460#64 →
      s.status = .Running →
      v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x24 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4484#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
          AllocCallPreserved s sm) := by
  have hbody := v2hsc_proto_decoder_dealloc_body_4460 hA s0 fsp out ptsPtr ptsCap x23_val hfsp_align
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 4448 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hbody ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hx21 hx24
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean_evs
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs st s _ hpc hrun hpres hx21 hx24) ?_
    intro evs1 s1 hevs1 hpc1 hrun1 ⟨hpres1, hx21_1, hx24_1, hacp1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx22_1, hx23_1, htr_1, hvregs_1⟩
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      refine ⟨evs1, hevs1, ?_, ?_⟩
      · simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)
      · exact ⟨by simp [v2hsc_Saved4436Preserved, wp_norm, arm64_norm, *],
               hacp1.trans (by simp [AllocCallPreserved, wp_norm, arm64_norm])⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine seq_clean_st (mid := entry + 4460#64)
        (P_mid := fun sm => arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x24 = (cur + 24#64) + 8#64 ∧
          AllocCallPreserved s1 sm) ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx22_1, hx23_1, htr_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx21_2, hx24_2, hacp2⟩
        have hrec := ih (cur + 24#64) (M.stepEvents evs1 st) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx21_2 hx24_2
        refine SepWP.mono hrec fun sf _Pf _ _ ⟨evs2, hevs2, hp, hpres_f, hacp_f⟩ => ?_
        refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hpres_f, (hacp1.trans hacp2).trans hacp_f⟩
        rw [AllocCostModel.stepEvents_append]
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        refine Entails.trans hp ?_
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

theorem v2hsc_dealloc_proto_decoder_4436
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4436#64)
    (hrun : s.status = .Running)
    (hpres : v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 pts.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4484#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ (if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
        AllocCallPreserved s sm) := by
  have hloop := v2hsc_proto_decoder_dealloc_loop_4460 hA s0 fsp out ptsPtr ptsCap x23_val hfsp_align
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 4436 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hloop hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  cases pts with
  | nil =>
    rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htr, hvregs⟩
    simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero, arrayAt, emp_sepConj] at hx21 ⊢
    apply sepWP_evs_nil
    simp only [AllocCostModel.stepEvents_nil]
    wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨?_, by simp [v2hsc_Saved4436Preserved, wp_norm, arm64_norm, *]⟩
    simp only [wp_norm, arm64_norm]
    exact Entails.of_eq (by sep_ac_rfl)
  | cons bs tl =>
    have hlen_pos : 0 < (bs :: tl).length := by simp
    have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
      have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
      omega
    have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
    have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
    simp only [hcap_ne, ↓reduceIte]
    refine seq_clean_st (mid := entry + 4460#64)
      (P_mid := fun sm => arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (bs :: tl) ∗
        A.pool lim st sm ∗ stackAt fsp allocHookStack ∗
        (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
         memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
           ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
         Frame))
      (Q := fun sm => v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x24 = ptsPtr + 8#64 ∧
        AllocCallPreserved s sm) ?_ ?_
    · rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htr, hvregs⟩
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      refine ⟨?_, by simp [v2hsc_Saved4436Preserved, wp_norm, arm64_norm, *]⟩
      simp only [wp_norm, arm64_norm]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx21_loop, hx24_loop, hacp_pre⟩
      have hsplit : ptsCap.toNat * 24 =
          (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 := by
        rw [← Nat.add_mul]; congr 1; omega
      have hbound : (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
        rw [← hsplit]; omega
      have hjoin : A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          memRegion ptsPtr ((bs :: tl).length * 24) ∗
          memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
            ((ptsCap.toNat - (bs :: tl).length) * 24) ⊢
          A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24) := by
        rw [hsplit, ProofLib.memRegion_split ptsPtr ((bs :: tl).length * 24)
          ((ptsCap.toNat - (bs :: tl).length) * 24) hbound]
        exact Entails.of_eq (by sep_ac_rfl)
      refine SepWP.mono
        (hloop (bs :: tl) ptsPtr st s_loop _
          (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
          hx21_loop hx24_loop)
        fun sm _Pm _ _ ⟨evs, hevs, hPm, hpres_m, hacp_m⟩ => ?_
      refine ⟨evs, hevs, Entails.trans hPm ?_, hpres_m, hacp_pre.trans hacp_m⟩
      refine Entails.trans
        (Entails.of_eq (show _ =
          (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion ptsPtr ((bs :: tl).length * 24) ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
             ((ptsCap.toNat - (bs :: tl).length) * 24)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame by sep_ac_rfl))
        (sepConj_mono_left hjoin)

theorem v2hsc_dealloc_proto_decoder_4484
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val w232 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4484#64)
    (hrun : s.status = .Running)
    (hpres : v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64) s
      ((if ptsCap = 0#64 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
        ((fsp + 232#64) ↦₆₄ w232) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ ((fsp + 232#64) ↦₆₄ w232) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
        AllocCallPreserved s sm) := by
  have hdealloc := v2hsc_sub_ok_dealloc_125316_fo hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 4484 32
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htr, hvregs⟩
  by_cases hc : ptsCap = 0#64
  · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
    simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx22 ⊢
    apply sepWP_evs_nil
    simp only [AllocCostModel.stepEvents_nil]
    wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨?_, by simp [v2hsc_Saved4436Preserved, wp_norm, arm64_norm, *]⟩
    simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)
  · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
    have hlsl := cap_mul_24 hpts_cap_lt
    simp only [hc, ↓reduceIte]
    apply sepWP_evs_dealloc (ptsCap.toNat * 24) 8
    wp_steps
    wp_apply
    have hacp_all : AllocCallPreserved s sf :=
      allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
    have ⟨_, _, _, _, _, _, _⟩ := hacp_all
    wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
    have hsp_sf' : sf.sp = fsp := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp])
    refine ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm]
      rw [← hsp_sf, hsp_sf']
      exact Entails.of_eq (by sep_ac_rfl)
    · simp [v2hsc_Saved4436Preserved, wp_norm, arm64_norm, hsp_sf', *]

theorem v2hsc_dealloc_some_proto_decoder_4428
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val w232 : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = ptsCap)
    (hx23 : s.readReg64 .x23 = x23_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64) s
      (((fsp + 232#64) ↦₆₄ w232) ∗
        ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
        ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
        (if ptsCap = 0 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
             ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ ((fsp + 232#64) ↦₆₄ w232) ∗
          ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = x23_val ∧
        TraceCalleeSaved sm s0 ∧
        AllocCallPreserved s sm) := by
  have h4436 := v2hsc_dealloc_proto_decoder_4436 hA s0
  have h4484 := v2hsc_dealloc_proto_decoder_4484 hA s0
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 4428 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at h4436 h4484 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  rcases htrace with ⟨htr, hvregs⟩
  refine seq_clean_st (mid := entry + 4436#64)
    (P_mid := fun sm => (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st sm ∗ stackAt fsp allocHookStack ∗
        (((fsp + 232#64) ↦₆₄ w232) ∗
         ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
         ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame))
    (Q := fun sm => v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
      sm.readReg64 .x21 = BitVec.ofNat 64 pts.length ∧
      AllocCallPreserved s sm)
    ?_ ?_
  · wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨?_, by simp [v2hsc_Saved4436Preserved, wp_norm, arm64_norm, *]⟩
    simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)
  · intro s1 hpc1 hrun1 ⟨hpres1, hx21_1, hacp1⟩
    have h1 := h4436 s1 fsp out ptsPtr ptsCap x23_val pts st
      (((fsp + 232#64) ↦₆₄ w232) ∗
       ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
       ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame)
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx21_1
    refine seq_clean_evs
      (P_evs := fun evs1 sm =>
        (if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗
          A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗
          (((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
           ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame))
      (Q := fun sm => v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
        AllocCallPreserved s1 sm)
      (SepWP.mono h1 fun sm _Pm _ _ ⟨evs1, hevs1, hPm, hpres_m, hacp_m⟩ =>
        ⟨evs1, hevs1, Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hpres_m, hacp_m⟩) ?_
    intro evs1 s2 hevs1 hpc2 hrun2 ⟨hpres2, hacp2⟩
    have h2 := h4484 s2 fsp out ptsPtr ptsCap x23_val w232 (M.stepEvents evs1 st)
      (((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
       ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame)
      hfsp_align hpts_cap_lt hpc2 hrun2 hpres2
    refine SepWP.mono h2 fun sm _Pm _ _ ⟨evs2, hevs2, hPm, hpres_m, hacp_m⟩ => ?_
    rcases hpres_m with ⟨hsp_m, hx19_m, _, _, hx23_m, htr_m⟩
    refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hsp_m, hx19_m, hx23_m, htr_m,
      (hacp1.trans hacp2).trans hacp_m⟩
    rw [AllocCostModel.stepEvents_append]
    exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscBudgetAux
