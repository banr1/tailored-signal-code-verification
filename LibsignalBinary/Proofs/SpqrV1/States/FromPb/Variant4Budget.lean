/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
public meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
meta import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueBudget -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
meta import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Fixed-Offset Budget Helpers for Variant 4 (`EkSentCt1Received`)

Fixed-offset `<EkSentCt1Received>::from_pb` specification, `+7084` error exit, and `FreeOnlyEvs`
inline `ProtoPolynomialDecoder` deallocation (`+5360..+5440 -> +7084`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4Budget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Drop (
  add_24_add_8 cap_mul_24 chunkedStatesSize cons_len_mul header_cells_entails_memRegion_24
  ofNat_add_one_beq_one_false_24 ofNat_beq_zero_false_24 ofNat_succ_eq_add_one
  sep_pull_body sep_push_body sep_rejoin_loop
  tail_len_mul_lt vecCapPtrDealloc vecU8_entails_capPtr_dealloc
)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.Unchunked (
  ekSentCt1ReceivedFromPbName extractLsb'_0_64_append extractLsb'_64_64_append
)
open CryptoVerification.SpqrV1.Layout.Stubs (
  fnOff_ek_sent_ct1_received_from_pb fnOff_poly_decoder_from_pb stubOff_rust_dealloc
)
open CryptoVerification.SpqrV1.States.FromPb (
  TraceCalleeSaved memRegion_out_928_split_32 out_8_32_entails_err_tail
  resultChunkedStatesAt spqrErrorByte statesFromPbName statesFromPbSavedCells
  statesFromPbStack statesFromPb_fnOff
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpecBase rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (
  DecoderFromPbOkExt decoderFromPbSpecBase
)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueBudget (states_from_pb_epilogue_60)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscBudgetAux (
  allocCallPreserved_of_step deallocFreeOnlySpec fnAddr_rebase_hooks_eq
  sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs seq_clean_st seq_vm_clean
  v2hsc_sub_ok_dealloc_125316_fo
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget (
  EkSentCt1ReceivedFromPbPostEnv EkSentCt1ReceivedFromPbPreEnv
  PbEkSentCt1Received ekSentCt1ReceivedFromPb
)
open scoped CryptoVerification.CodeLayout
open scoped LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueBudget

/-! ## Re-exports from `Variant4` -/

abbrev v4_Saved5368Preserved := CryptoVerification.SpqrV1.States.FromPb.v4_Saved5368Preserved

alias v4_sepWPp_seq_clean := CryptoVerification.SpqrV1.States.FromPb.v4_sepWPp_seq_clean
alias v4_onPanic_frame_entails := CryptoVerification.SpqrV1.States.FromPb.v4_onPanic_frame_entails
alias v4_sepWPp_call_ret := CryptoVerification.SpqrV1.States.FromPb.v4_sepWPp_call_ret
alias v4_fnAddr_eq_sub_of_rel := CryptoVerification.SpqrV1.States.FromPb.v4_fnAddr_eq_sub_of_rel
alias v4_stackAt_encoderFromPbStack_to_allocHook :=
  CryptoVerification.SpqrV1.States.FromPb.v4_stackAt_encoderFromPbStack_to_allocHook
alias v4_stackAt_allocHook_to_encoderFromPbStack :=
  CryptoVerification.SpqrV1.States.FromPb.v4_stackAt_allocHook_to_encoderFromPbStack
alias v4_ptsCap_add_one_ne_zero := CryptoVerification.SpqrV1.States.FromPb.v4_ptsCap_add_one_ne_zero

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff fnOff_ek_sent_ct1_received_from_pb fnOff_poly_decoder_from_pb
  stubOff_rust_dealloc TraceCalleeSaved

/-! ## Budget-Threaded Subroutine Call Bridges & Error Exit (`+7084`) -/

/-- Unplaced (`PL=False`) envelope-parameterized budget-threaded specification of
    `<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb` (Block `348`). -/
def hpeers_ekSentCt1ReceivedFromPbSpecOfEnvBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (PreEnv PostEnv : PbEkSentCt1Received → List AllocEvent → Prop) :
    Spec (CryptoVerification.SpqrV1.Unchunked.EkSentCt1ReceivedFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      LibsignalBinary.Heap.FitsEnv M lim st (PreEnv x.pb)⌝ ∗
      memRegion x.out 104 ∗
      CryptoVerification.SpqrV1.Drop.protoUnchunkedEkSentCt1ReceivedAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp CryptoVerification.SpqrV1.Unchunked.ekSentCt1ReceivedFromPbStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      CryptoVerification.SpqrV1.Unchunked.ekSentCt1ReceivedResultAt A.repAlloc x.out
        (ekSentCt1ReceivedFromPb (CryptoVerification.LibsignalSpqrV1.spqrAuthApi F) x.pb) ∗
      memRegion x.pbA 104 ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x.pb evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp CryptoVerification.SpqrV1.Unchunked.ekSentCt1ReceivedFromPbStack

/-- Unplaced (`PL=False`) canonical budget-threaded specification of
    `<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb` (Block `348`). -/
def hpeers_ekSentCt1ReceivedFromPbSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (CryptoVerification.SpqrV1.Unchunked.EkSentCt1ReceivedFromPbGhost × M.σ) :=
  hpeers_ekSentCt1ReceivedFromPbSpecOfEnvBase M A lim F
    (EkSentCt1ReceivedFromPbPreEnv F) (EkSentCt1ReceivedFromPbPostEnv F)

/-- Fixed-offset `<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb` meets
`hpeers_ekSentCt1ReceivedFromPbSpecBase M A lim F` on `tripleRatchetProgAtExt b ext`. -/
def EkSentCt1ReceivedFromPbOkExt (b : BitVec 64) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedFromPbName)
    (hpeers_ekSentCt1ReceivedFromPbSpecBase M A lim F)

theorem v4_sub_ok_dealloc_125316
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc"))
      (rustCliDeallocBudgetSpecBase M A lim) :=
  hA.dealloc_ok_at statesFromPbName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc"))

theorem v4_sub_ok_dealloc_125316_fo
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc"))
      (deallocFreeOnlySpec M A lim) :=
  v2hsc_sub_ok_dealloc_125316_fo hA

private theorem sub_ok_of_addr_eq {P : Program} {a1 a2 : BitVec 64} {α : Type} {S : Spec α}
    (heq : a1 = a2) (h : subroutine_ok P a1 S) : subroutine_ok P a2 S :=
  heq ▸ h

theorem v4_sub_ok_ek_sent_ct1_received_from_pb
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hek : EkSentCt1ReceivedFromPbOkExt b M A lim F ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 18368#64)
      (hpeers_ekSentCt1ReceivedFromPbSpecBase M A lim F) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb"
        "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb"))
      (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff fnOff_ek_sent_ct1_received_from_pb (by decide))
    hek

theorem v4_sub_ok_decoder_from_pb
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdec : DecoderFromPbOkExt b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 35448#64)
      (decoderFromPbSpecBase M A lim) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb"
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb"))
      (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff fnOff_poly_decoder_from_pb (by decide))
    hdec

set_option maxHeartbeats 800000 in
/-- Shared `Err(err)` exit at `+7084` (`0x5bc50 -> s0.x30`):
when `x28` has low byte `spqrErrorByte err` and `x19 = out`, writes `x26, x24` to `[out + 16..32]`,
sets `x8 = noneCap`, writes `x28` to `[out + 8]`, and branches to `+60`, preserving
`VmPreserved s1 sf` and `AllocCallPreserved s1 sf`. -/
theorem v4_states_from_pb_err_7084
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : CryptoVerification.LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7084#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx28_1 : (s1.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err)
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
  rcases htr1 with ⟨htr_1, hvregs_1⟩
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
  · states_from_pb_fetches_range_b b trapHooks 7084 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_vm_steps {
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      refine ⟨by simp [wp_norm, arm64_norm], ?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, noneCap, *]⟩
      have htail := out_8_32_entails_err_tail out (s1.readReg64 .x28)
        (s1.readReg64 .x26) (s1.readReg64 .x24)
      rw [hx28_1] at htail
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((out + 8#64) ↦₆₄ s1.readReg64 .x28) ∗
           ((out + 16#64) ↦₆₄ s1.readReg64 .x26) ∗
           ((out + 24#64) ↦₆₄ s1.readReg64 .x24) ∗
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

/-! ## Budget-Threaded `ProtoPolynomialDecoder` Deallocation Loop (`+5360..+5440 -> +7084`) -/

theorem v4_proto_decoder_dealloc_body_5392
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5392#64 →
      s.status = .Running →
      v4_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x22 = cnt →
      s.readReg64 .x23 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5380#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v4_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x22 = cnt ∧
          sm.readReg64 .x23 = cur + 8#64 ∧
          AllocCallPreserved s sm) := by
  have hdealloc := v4_sub_ok_dealloc_125316_fo hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 5392 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro cur cnt bs st s Frame hpc hrun hpres hx22 hx23
  rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htr, hvregs⟩
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
    refine ⟨?_, by simp [v4_Saved5368Preserved, CryptoVerification.SpqrV1.States.FromPb.v4_Saved5368Preserved, wp_norm, arm64_norm, *]⟩
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
    · simp [v4_Saved5368Preserved, CryptoVerification.SpqrV1.States.FromPb.v4_Saved5368Preserved, wp_norm, arm64_norm, hsp_sf', *]

theorem v4_proto_decoder_dealloc_loop_5392
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5392#64 →
      s.status = .Running →
      v4_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x23 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5416#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v4_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          AllocCallPreserved s sm) := by
  have hbody := v4_proto_decoder_dealloc_body_5392 hA s0 fsp out ptsPtr ptsCap x28_val hfsp_align
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 5380 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hbody ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = fnEntry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hx22 hx23
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean_evs
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs st s _ hpc hrun hpres hx22 hx23) ?_
    intro evs1 s1 hevs1 hpc1 hrun1 ⟨hpres1, hx22_1, hx23_1, hacp1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx22_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx21_1, hx28_1, htr_1, hvregs_1⟩
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      refine ⟨evs1, hevs1, ?_, ?_⟩
      · simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)
      · exact ⟨by simp [v4_Saved5368Preserved, CryptoVerification.SpqrV1.States.FromPb.v4_Saved5368Preserved, wp_norm, arm64_norm, *],
               hacp1.trans (by simp [AllocCallPreserved, wp_norm, arm64_norm])⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx22_1
      refine seq_clean_st (mid := fnEntry + 5392#64)
        (P_mid := fun sm => arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v4_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x23 = (cur + 24#64) + 8#64 ∧
          AllocCallPreserved s1 sm) ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx21_1, hx28_1, htr_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
        refine ⟨?_, by simp [v4_Saved5368Preserved, CryptoVerification.SpqrV1.States.FromPb.v4_Saved5368Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
        simp only [wp_norm, arm64_norm]; exact Entails.refl _
      · intro s2 hpc2 hrun2 ⟨hpres2, hx22_2, hx23_2, hacp2⟩
        have hrec := ih (cur + 24#64) (M.stepEvents evs1 st) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx22_2 hx23_2
        refine SepWP.mono hrec fun sf _Pf _ _ ⟨evs2, hevs2, hp, hpres_f, hacp_f⟩ => ?_
        refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hpres_f, (hacp1.trans hacp2).trans hacp_f⟩
        rw [AllocCostModel.stepEvents_append]
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        refine Entails.trans hp ?_
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

/-- Shared `ProtoPolynomialDecoder` inline deallocation at `+5368 -> +7084` (`0x5b59c -> 0x5bc50`):
when `x21 = ptsCap`, `x20 = ptsPtr`, `x22 = BitVec.ofNat 64 pts.length`, deallocates all `Vec<u8>`
elements in `pts` and the `pts` buffer itself, then jumps to `+7084`. -/
theorem v4_states_from_pb_dealloc_proto_decoder_5368
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5368#64)
    (hrun : s.status = .Running)
    (hpres : v4_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 pts.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7084#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
        AllocCallPreserved s sm) := by
  have hdealloc := v4_sub_ok_dealloc_125316_fo hA
  have hloop := v4_proto_decoder_dealloc_loop_5392 hA s0 fsp out ptsPtr ptsCap x28_val hfsp_align
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 5368 12
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 5416 28
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hloop hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = fnEntry
  examples_hide_fetches
  refine seq_clean_evs (mid := fnEntry + 5416#64)
    (P_evs := fun evs1 sm =>
      (if ptsCap = 0#64 then emp
       else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v4_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧ AllocCallPreserved s sm)
    ?_ ?_
  · cases pts with
    | nil =>
      rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htr, hvregs⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj] at hx22 ⊢
      apply sepWP_evs_nil
      simp only [AllocCostModel.stepEvents_nil]
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      refine ⟨?_, by simp [v4_Saved5368Preserved, CryptoVerification.SpqrV1.States.FromPb.v4_Saved5368Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
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
      refine seq_clean_st (mid := fnEntry + 5392#64)
        (P_mid := fun sm => arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (bs :: tl) ∗
          A.pool lim st sm ∗ stackAt fsp allocHookStack ∗
          (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
             ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
           Frame))
        (Q := fun sm => v4_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (bs :: tl).length ∧
          sm.readReg64 .x23 = ptsPtr + 8#64 ∧
          AllocCallPreserved s sm) ?_ ?_
      · rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htr, hvregs⟩
        wp_steps
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
        refine ⟨?_, by simp [v4_Saved5368Preserved, CryptoVerification.SpqrV1.States.FromPb.v4_Saved5368Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
        simp only [wp_norm, arm64_norm]
        exact Entails.of_eq (by sep_ac_rfl)
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx22_loop, hx23_loop, hacp_pre⟩
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
            hx22_loop hx23_loop)
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
  · intro evs1 s3 hevs1 hpc3 hrun3 ⟨⟨hsp_3, hx19_3, hx20_3, hx21_3, hx28_3, htr_3, hvregs_3⟩, hacp1⟩
    let st1 := M.stepEvents evs1 st
    by_cases hc : ptsCap = 0#64
    · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
      simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx21_3 ⊢
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun3])
      refine ⟨evs1, hevs1, ?_, ?_⟩
      · simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)
      · exact ⟨by simp [v4_Saved5368Preserved, CryptoVerification.SpqrV1.States.FromPb.v4_Saved5368Preserved, wp_norm, arm64_norm, *],
               hacp1.trans (by simp [AllocCallPreserved, wp_norm, arm64_norm])⟩
    · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      have hlsl := cap_mul_24 hpts_cap_lt
      simp only [hc, ↓reduceIte]
      wp_steps
      wp_apply
      have hacp2 : AllocCallPreserved s3 sf :=
        allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
      have ⟨_, _, _, _, _, _, _⟩ := hacp2
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
      have hsp_sf' : sf.sp = fsp := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp_3])
      refine ⟨evs1 ++ rustDeallocEvents (ptsCap.toNat * 24) 8,
        hevs1.append (FreeOnlyEvs.singleton 8 (ptsCap.toNat * 24)), ?_, ?_⟩
      · simp only [st1, AllocCostModel.stepEvents_append, wp_norm, arm64_norm]
        rw [← hsp_sf, hsp_sf']
        exact Entails.of_eq (by sep_ac_rfl)
      · exact ⟨by simp [v4_Saved5368Preserved, CryptoVerification.SpqrV1.States.FromPb.v4_Saved5368Preserved, wp_norm, arm64_norm, hsp_sf', *],
               (hacp1.trans hacp2).trans (by simp [AllocCallPreserved, wp_norm, arm64_norm])⟩

/-- Shared `Option<ProtoPolynomialDecoder>` inline `None` deallocation at `+5360 -> +7084`,
preserving `VmPreserved` and `AllocCallPreserved`. -/
theorem v4_states_from_pb_dealloc_none_proto_decoder_5360
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x28_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v4_Saved5368Preserved s0 s fsp out ptsPtr noneCap x28_val) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7084#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        VmPreserved s sm ∧
        AllocCallPreserved s sm ∧
        v4_Saved5368Preserved s0 sm fsp out ptsPtr noneCap x28_val) := by
  rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htr, hvregs⟩
  change s.readReg64 .x21 = 0xffffffffffffffff#64 at hx21
  have hwp : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7084#64) s P
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ P) ∧
        (AllocCallPreserved s sm ∧
         v4_Saved5368Preserved s0 sm fsp out ptsPtr noneCap x28_val)) := by
    states_from_pb_fetches_range_b b trapHooks 5360 8
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_vm_steps {
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      refine ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
        by simp [v4_Saved5368Preserved, CryptoVerification.SpqrV1.States.FromPb.v4_Saved5368Preserved,
          AllocCallPreserved, noneCap, wp_norm, arm64_norm, *]⟩
    }
  exact SepWP.mono hwp fun _ _ _ _ ⟨hvm, hP, hacp, hpres'⟩ => ⟨hP, hvm, hacp, hpres'⟩

/-- Shared `Option<ProtoPolynomialDecoder>` inline `Some` deallocation at `+5360 -> +7084`. -/
theorem v4_states_from_pb_dealloc_some_proto_decoder_5360
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v4_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 pts.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7084#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
        AllocCallPreserved s sm) := by
  have h5368 := v4_states_from_pb_dealloc_proto_decoder_5368 hA s0
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 5360 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at h5368 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = fnEntry
  examples_hide_fetches
  refine seq_clean_st (mid := fnEntry + 5368#64)
    (P_mid := fun sm => (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v4_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
      sm.readReg64 .x22 = BitVec.ofNat 64 pts.length ∧
      AllocCallPreserved s sm)
    ?_ ?_
  · rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htr, hvregs⟩
    have hne := v4_ptsCap_add_one_ne_zero hpts_cap_lt
    wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨?_, by simp [v4_Saved5368Preserved, CryptoVerification.SpqrV1.States.FromPb.v4_Saved5368Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
    simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)
  · intro s1 hpc1 hrun1 ⟨hpres1, hx22_1, hacp1⟩
    refine SepWP.mono
      (h5368 s1 fsp out ptsPtr ptsCap x28_val pts st Frame
        hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx22_1)
      fun sm _Pm _ _ ⟨evs, hevs, hPm, hpres_m, hacp2⟩ =>
        ⟨evs, hevs, hPm, hpres_m, hacp1.trans hacp2⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4Budget
