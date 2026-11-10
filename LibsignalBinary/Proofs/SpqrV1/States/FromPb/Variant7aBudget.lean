/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4Budget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7a
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aBudgetAux
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
# Budget-Threaded Variant 7 (`Ct1Sampled`, `+1056`) — Part A

Fixed-offset budget-threaded subroutine call bridges, `+4632` error exit (`+4632 -> +7084 -> s0.x30`),
and inline `ProtoPolynomialDecoder` deallocation (`+4556..+4632`) under `FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecU8)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Drop (
  add_24_add_8 cap_mul_24 chunkedStatesSize cons_len_mul header_cells_entails_memRegion_24
  ofNat_add_one_beq_one_false_24 ofNat_beq_zero_false_24 ofNat_succ_eq_add_one
  protoPolyDecoderHeaders_entails_memRegion_40 sep_pull_body sep_push_body sep_rejoin_loop
  tail_len_mul_lt vecCapPtrDealloc vecU8_entails_capPtr_dealloc
)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbName encoderFromPbStack)
open CryptoVerification.SpqrV1.Unchunked (
  ct1SentFromPbName extractLsb'_0_64_append extractLsb'_64_64_append
)
open CryptoVerification.SpqrV1.Layout.Stubs (
  fnOff_ct1_sent_from_pb fnOff_drop_ct1_sent_local2 fnOff_drop_poly16
  fnOff_drop_poly_encoder_local2 fnOff_drop_proto_ct1_sent_ek_received
  fnOff_drop_proto_poly_encoder fnOff_poly_encoder_from_pb
  stubOff_handle_error stubOff_memcpy stubOff_rust_alloc stubOff_rust_dealloc
  stubOff_rust_no_alloc_shim
)
open CryptoVerification.SpqrV1.States.FromPb (
  TraceCalleeSaved resultChunkedStatesAt spqrErrorByte statesFromPbName
  statesFromPbSavedCells statesFromPbStack statesFromPb_fnOff
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpecBase rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (dropGluePoly16Spec dropGluePoly16SpecBase)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget (dropGluePolyEncoderSpec dropGluePolyEncoderSpecBase)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec dropProtoPolyEncoderSpecBase)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (
  dropProtoUnchunkedCt1SentEkReceivedSpecBase dropUnchunkedCt1SentSpecBase
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget (
  EncoderFromPbOkExt encoderFromPbSpecBase
)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscBudgetAux (
  allocCallPreserved_of_step deallocFreeOnlySpec fnAddr_rebase_hooks_eq
  sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs seq_clean_st seq_vm_clean
)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdBudgetAux (
  drop_glue_poly16_ok_ext drop_glue_poly_encoder_local2_ok_ext
)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4Budget (
  v4_fnAddr_eq_sub_of_rel v4_stackAt_allocHook_to_encoderFromPbStack
  v4_stackAt_encoderFromPbStack_to_allocHook v4_states_from_pb_err_7084
  v4_sub_ok_dealloc_125316_fo
)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aBudgetAux (
  drop_glue_proto_poly_encoder_ok_ext drop_proto_unchunked_ct1_sent_ek_received_ok_ext
  drop_unchunked_ct1_sent_local2_ok_ext
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget (
  Ct1SentFromPbPostEnv Ct1SentFromPbPreEnv PbCt1Sent ct1SentFromPb
)
open scoped CryptoVerification.CodeLayout
open scoped LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueBudget

/-! ## Re-exports from `Variant7a` -/

abbrev v7_Saved4560Preserved := CryptoVerification.SpqrV1.States.FromPb.v7_Saved4560Preserved

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  fnOff_drop_proto_ct1_sent_ek_received fnOff_drop_proto_poly_encoder
  fnOff_drop_poly16 fnOff_drop_poly_encoder_local2 fnOff_drop_ct1_sent_local2
  fnOff_poly_encoder_from_pb fnOff_ct1_sent_from_pb
  stubOff_rust_no_alloc_shim stubOff_rust_alloc stubOff_rust_dealloc
  stubOff_memcpy stubOff_handle_error TraceCalleeSaved

/-! ## 1. Budget-Threaded Subroutine Call Bridges for Variant 7 -/

/-- Unplaced (`PL=False`) envelope-parameterized budget-threaded specification of
    `<spqr::v1::unchunked::send_ct::Ct1Sent>::from_pb` (Block `339`). -/
def hpeers_ct1SentFromPbSpecOfEnvBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (PreEnv PostEnv : PbCt1Sent → List AllocEvent → Prop) :
    Spec (CryptoVerification.SpqrV1.Unchunked.Ct1SentFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      LibsignalBinary.Heap.FitsEnv M lim st (PreEnv x.pb)⌝ ∗
      memRegion x.out 128 ∗
      CryptoVerification.SpqrV1.Drop.protoUnchunkedCt1SentAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp CryptoVerification.SpqrV1.Unchunked.ct1SentFromPbStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      CryptoVerification.SpqrV1.Unchunked.ct1SentResultAt A.repAlloc x.out
        (ct1SentFromPb (CryptoVerification.LibsignalSpqrV1.spqrAuthApi F) x.pb) ∗
      memRegion x.pbA 128 ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x.pb evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp CryptoVerification.SpqrV1.Unchunked.ct1SentFromPbStack

/-- Unplaced (`PL=False`) canonical budget-threaded specification of
    `<spqr::v1::unchunked::send_ct::Ct1Sent>::from_pb` (Block `339`). -/
def hpeers_ct1SentFromPbSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (CryptoVerification.SpqrV1.Unchunked.Ct1SentFromPbGhost × M.σ) :=
  hpeers_ct1SentFromPbSpecOfEnvBase M A lim F (Ct1SentFromPbPreEnv F) (Ct1SentFromPbPostEnv F)

/-- Fixed-offset `<spqr::v1::unchunked::send_ct::Ct1Sent>::from_pb` meets
`hpeers_ct1SentFromPbSpecBase M A lim F` on `tripleRatchetProgAtExt b ext`. -/
def Ct1SentFromPbOkExt (b : BitVec 64) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr ct1SentFromPbName)
    (hpeers_ct1SentFromPbSpecBase M A lim F)

private theorem sub_ok_of_addr_eq {P : Program} {a1 a2 : BitVec 64} {α : Type} {S : Spec α}
    (heq : a1 = a2) (h : subroutine_ok P a1 S) : subroutine_ok P a2 S :=
  heq ▸ h

private theorem v7_add_1092_sub_54872_eq (x : BitVec 64) :
    x + 1092#64 + 18446744073709496744#64 = x - 53780#64 := by bv_omega

theorem v7_sub_ok_drop_proto_unchunked_ct1_sent_ek_received
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1092#64 + 18446744073709496744#64)
      (dropProtoUnchunkedCt1SentEkReceivedSpecBase M A lim) :=
  sub_ok_of_addr_eq
    (by
      rw [v7_add_1092_sub_54872_eq]
      exact v4_fnAddr_eq_sub_of_rel (Program.fnAddr_rel (k := 53780) (b := b) (X := Rust.withPanics ext)
        fnOff_drop_proto_ct1_sent_ek_received statesFromPb_fnOff (by decide)))
    (drop_proto_unchunked_ct1_sent_ek_received_ok_ext (b := b) (A := A) (lim := lim) (ext := ext) hA)

private theorem v7_add_4544_sub_60772_eq (x : BitVec 64) :
    x + 4544#64 + 18446744073709490844#64 = x - 56228#64 := by bv_omega

theorem v7_sub_ok_drop_proto_poly_encoder
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4544#64 + 18446744073709490844#64)
      (dropProtoPolyEncoderSpecBase M A lim) :=
  sub_ok_of_addr_eq
    (by
      rw [v7_add_4544_sub_60772_eq]
      exact v4_fnAddr_eq_sub_of_rel (Program.fnAddr_rel (k := 56228) (b := b) (X := Rust.withPanics ext)
        fnOff_drop_proto_poly_encoder statesFromPb_fnOff (by decide)))
    (drop_glue_proto_poly_encoder_ok_ext (b := b) (A := A) (lim := lim) (ext := ext) hA)

private theorem v7_add_10564_sub_68396_eq (x : BitVec 64) :
    x + 10564#64 + 18446744073709483220#64 = x - 57832#64 := by bv_omega

theorem v7_sub_ok_drop_poly16
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10564#64 + 18446744073709483220#64)
      (dropGluePoly16SpecBase M A lim) :=
  sub_ok_of_addr_eq
    (by
      rw [v7_add_10564_sub_68396_eq]
      exact v4_fnAddr_eq_sub_of_rel (Program.fnAddr_rel (k := 57832) (b := b) (X := Rust.withPanics ext)
        fnOff_drop_poly16 statesFromPb_fnOff (by decide)))
    (drop_glue_poly16_ok_ext (b := b) (A := A) (lim := lim) (ext := ext) hA)

private theorem v7_add_11100_sub_67120_eq (x : BitVec 64) :
    x + 11100#64 + 18446744073709484496#64 = x - 56020#64 := by bv_omega

theorem v7_sub_ok_drop_poly_encoder_local2
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11100#64 + 18446744073709484496#64)
      (dropGluePolyEncoderSpecBase M A lim) :=
  sub_ok_of_addr_eq
    (by
      rw [v7_add_11100_sub_67120_eq]
      exact v4_fnAddr_eq_sub_of_rel (Program.fnAddr_rel (k := 56020) (b := b) (X := Rust.withPanics ext)
        fnOff_drop_poly_encoder_local2 statesFromPb_fnOff (by decide)))
    (drop_glue_poly_encoder_local2_ok_ext (b := b) (A := A) (lim := lim) (ext := ext) hA)

private theorem v7_add_11108_sub_66156_eq (x : BitVec 64) :
    x + 11108#64 + 18446744073709485460#64 = x - 55048#64 := by bv_omega

theorem v7_sub_ok_drop_unchunked_ct1_sent_local2
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11108#64 + 18446744073709485460#64)
      (dropUnchunkedCt1SentSpecBase M A lim F) :=
  sub_ok_of_addr_eq
    (by
      rw [v7_add_11108_sub_66156_eq]
      exact v4_fnAddr_eq_sub_of_rel (Program.fnAddr_rel (k := 55048) (b := b) (X := Rust.withPanics ext)
        fnOff_drop_ct1_sent_local2 statesFromPb_fnOff (by decide)))
    (drop_unchunked_ct1_sent_local2_ok_ext (b := b) (A := A) (lim := lim) (F := F) (ext := ext) hA)

theorem v7_sub_ok_encoder_from_pb
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (henc : EncoderFromPbOkExt b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 32996#64)
      (encoderFromPbSpecBase M A lim) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 32996) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff fnOff_poly_encoder_from_pb (by decide))
    henc

theorem v7_sub_ok_ct1_sent_from_pb
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hct1 : Ct1SentFromPbOkExt b M A lim F ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 15272#64)
      (hpeers_ct1SentFromPbSpecBase M A lim F) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 15272) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff fnOff_ct1_sent_from_pb (by decide))
    hct1

/-! ## 2. Error Exit at `+4632` (`bfi x28, x23, #8, #56; b +7084`) -/

@[local simp, local arm64_norm, local wp_norm]
private theorem v7_bfi_8_56_extractLsb_0_8 (x28 x23 : BitVec 64) :
    (x28 &&& 255#64 ||| (x23 &&& 72057594037927935#64) <<< 8).extractLsb' 0 8 =
      x28.extractLsb' 0 8 := by bv_kernel

/-- Error exit at `+4632` (`0x5b2bc -> +7084 -> s0.x30`):
given `(s1.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err`, executes `bfi x28, x23, #8, #56`,
jumps to `+7084`, and returns `Err(err)`, preserving `VmPreserved s1 sf` and `AllocCallPreserved s1 sf`. -/
theorem v7_err_4632
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : CryptoVerification.LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64)
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
  refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7084#64)
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
      (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range_b b trapHooks 4632 8
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_vm_steps {
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      exact ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
        by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
    }
  · intro s2 hpc2 hrun2 hvm2 ⟨hacp2, hsp2, hx19_2, hx28_2, htr2⟩
    exact SepWP.mono
      (v4_states_from_pb_err_7084 s0 s2 out err Rest hsp0_align hpc2 hrun2 hsp2 hx19_2 hx28_2 htr2)
      fun sf _Pf _ _ ⟨hPf, hvm_f, hacp_f, hsp_f, hcc_f, htr_f⟩ =>
        ⟨hPf, hvm2.trans hvm_f, hacp2.trans hacp_f, hsp_f, hcc_f, htr_f⟩

/-! ## 3. Budget-Threaded `ProtoPolynomialDecoder` Inline Deallocation at `+4556..+4632` -/

theorem v7_proto_decoder_dealloc_body_4584
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4584#64 →
      s.status = .Running →
      v7_Saved4560Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x25 = cnt →
      s.readReg64 .x27 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4572#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x25 = cnt ∧
          sm.readReg64 .x27 = cur + 8#64 ∧
          AllocCallPreserved s sm) := by
  have hdealloc := v4_sub_ok_dealloc_125316_fo hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 4584 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro cur cnt bs st s Frame hpc hrun hpres hx25 hx27
  rcases hpres with ⟨hsp, hx19, hx20, hx22, hx28, htr, hvregs⟩
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
    refine ⟨?_, by simp [v7_Saved4560Preserved, CryptoVerification.SpqrV1.States.FromPb.v7_Saved4560Preserved, wp_norm, arm64_norm, *]⟩
    try simp only [wp_norm, arm64_norm]
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
    · simp [v7_Saved4560Preserved, CryptoVerification.SpqrV1.States.FromPb.v7_Saved4560Preserved, wp_norm, arm64_norm, hsp_sf', *]

theorem v7_proto_decoder_dealloc_loop_4584
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4584#64 →
      s.status = .Running →
      v7_Saved4560Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x25 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x27 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4608#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          AllocCallPreserved s sm) := by
  have hbody := v7_proto_decoder_dealloc_body_4584 hA s0 fsp out ptsPtr ptsCap x28_val hfsp_align
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 4572 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hbody ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = fnEntry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hx25 hx27
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean_evs
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs st s _ hpc hrun hpres hx25 hx27) ?_
    intro evs1 s1 hevs1 hpc1 hrun1 ⟨hpres1, hx25_1, hx27_1, hacp1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx25_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx22_1, hx28_1, htr_1, hvregs_1⟩
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      refine ⟨evs1, hevs1, ?_, ?_⟩
      · try simp only [wp_norm, arm64_norm]
        exact Entails.of_eq (by sep_ac_rfl)
      · exact ⟨by simp [v7_Saved4560Preserved, CryptoVerification.SpqrV1.States.FromPb.v7_Saved4560Preserved, wp_norm, arm64_norm, *],
               hacp1.trans (by simp [AllocCallPreserved, wp_norm, arm64_norm])⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx25_1
      refine seq_clean_st (mid := fnEntry + 4584#64)
        (P_mid := fun sm => arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x25 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x27 = (cur + 24#64) + 8#64 ∧
          AllocCallPreserved s1 sm) ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx22_1, hx28_1, htr_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
        refine ⟨?_, by simp [v7_Saved4560Preserved, CryptoVerification.SpqrV1.States.FromPb.v7_Saved4560Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
        simp only [wp_norm, arm64_norm]; exact Entails.refl _
      · intro s2 hpc2 hrun2 ⟨hpres2, hx25_2, hx27_2, hacp2⟩
        have hrec := ih (cur + 24#64) (M.stepEvents evs1 st) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx25_2 hx27_2
        refine SepWP.mono hrec fun sf _Pf _ _ ⟨evs2, hevs2, hp, hpres_f, hacp_f⟩ => ?_
        refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hpres_f, (hacp1.trans hacp2).trans hacp_f⟩
        rw [AllocCostModel.stepEvents_append]
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        refine Entails.trans hp ?_
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

theorem v7_proto_decoder_dealloc_4560
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4560#64)
    (hrun : s.status = .Running)
    (hpres : v7_Saved4560Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 pts.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
        AllocCallPreserved s sm) := by
  have hdealloc := v4_sub_ok_dealloc_125316_fo hA
  have hloop := v7_proto_decoder_dealloc_loop_4584 hA s0 fsp out ptsPtr ptsCap x28_val hfsp_align
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 4560 12
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 4608 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hloop hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = fnEntry
  examples_hide_fetches
  refine seq_clean_evs (mid := fnEntry + 4608#64)
    (P_evs := fun evs1 sm =>
      (if ptsCap = 0#64 then emp
       else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧ AllocCallPreserved s sm)
    ?_ ?_
  · cases pts with
    | nil =>
      rcases hpres with ⟨hsp, hx19, hx20, hx22, hx28, htr, hvregs⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj] at hx25 ⊢
      apply sepWP_evs_nil
      simp only [AllocCostModel.stepEvents_nil]
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      refine ⟨?_, by simp [v7_Saved4560Preserved, CryptoVerification.SpqrV1.States.FromPb.v7_Saved4560Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
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
      refine seq_clean_st (mid := fnEntry + 4584#64)
        (P_mid := fun sm => arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (bs :: tl) ∗
          A.pool lim st sm ∗ stackAt fsp allocHookStack ∗
          (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
             ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
           Frame))
        (Q := fun sm => v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x25 = BitVec.ofNat 64 (bs :: tl).length ∧
          sm.readReg64 .x27 = ptsPtr + 8#64 ∧
          AllocCallPreserved s sm) ?_ ?_
      · rcases hpres with ⟨hsp, hx19, hx20, hx22, hx28, htr, hvregs⟩
        wp_steps
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
        refine ⟨?_, by simp [v7_Saved4560Preserved, CryptoVerification.SpqrV1.States.FromPb.v7_Saved4560Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
        simp only [wp_norm, arm64_norm]
        exact Entails.of_eq (by sep_ac_rfl)
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx25_loop, hx27_loop, hacp_pre⟩
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
            hx25_loop hx27_loop)
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
  · intro evs1 s3 hevs1 hpc3 hrun3 ⟨⟨hsp_3, hx19_3, hx20_3, hx22_3, hx28_3, htr_3, hvregs_3⟩, hacp1⟩
    let st1 := M.stepEvents evs1 st
    by_cases hc : ptsCap = 0#64
    · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
      simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx22_3 ⊢
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun3])
      refine ⟨evs1, hevs1, ?_, ?_⟩
      · try simp only [wp_norm, arm64_norm]
        exact Entails.of_eq (by sep_ac_rfl)
      · exact ⟨by simp [v7_Saved4560Preserved, CryptoVerification.SpqrV1.States.FromPb.v7_Saved4560Preserved, wp_norm, arm64_norm, *],
               hacp1.trans (by simp [AllocCallPreserved, wp_norm, arm64_norm])⟩
    · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      have hlsl := cap_mul_24 hpts_cap_lt
      simp only [hc, ↓reduceIte]
      wp_steps
      wp_apply
      have hacp2 : AllocCallPreserved s3 sf :=
        allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
      have ⟨_, _, _, _, _, _, _⟩ := hacp2
      apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
      have hsp_sf' : sf.sp = fsp := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp_3])
      refine ⟨evs1 ++ rustDeallocEvents (ptsCap.toNat * 24) 8,
        hevs1.append (FreeOnlyEvs.singleton 8 (ptsCap.toNat * 24)), ?_, ?_⟩
      · simp only [st1, AllocCostModel.stepEvents_append, wp_norm, arm64_norm]
        rw [← hsp_sf, hsp_sf']
        exact Entails.of_eq (by sep_ac_rfl)
      · exact ⟨by simp [v7_Saved4560Preserved, CryptoVerification.SpqrV1.States.FromPb.v7_Saved4560Preserved, wp_norm, arm64_norm, hsp_sf', *],
               (hacp1.trans hacp2).trans (by simp [AllocCallPreserved, wp_norm, arm64_norm])⟩

/-- Deallocates `ProtoPolynomialDecoder` at `pbA + 184#64` starting at `+4556` (`ldp x20, x25, [x27, #0xc0]`):
given `x27 = pbA` and `x22 = ptsCap`, loads `ptsPtr, pts.length`, runs the loop `+4560..+4632`,
and collapses `pbA + 184..224` into `memRegion (pbA + 184#64) 40`, reaching `+4632` with `FreeOnlyEvs`. -/
theorem v7_proto_decoder_dealloc_4556
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s1 : State) (out pbA ptsCap ptsPtr x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4556#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = ptsCap)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ ptsCap) ∗
         ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         (if ptsCap = 0 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
              ((ptsCap.toNat - pts.length) * 24)) ∗
         memRegion (pbA + 208#64) 16) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        AllocCallPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  rcases htr1 with ⟨htr_1, hvregs_1⟩
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4560#64)
    (P_mid :=
      (if ptsCap = 0 then emp
       else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
         memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
           ((ptsCap.toNat - pts.length) * 24)) ∗
      A.pool lim st s1 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
       ((pbA + 184#64) ↦₆₄ ptsCap) ∗
       ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       memRegion (pbA + 208#64) 16 ∗
       Frame))
    (Q := fun sm =>
      v7_Saved4560Preserved s0 sm (s0.sp - 2400#64) out ptsPtr ptsCap x28_val ∧
      sm.readReg64 .x25 = BitVec.ofNat 64 pts.length ∧
      AllocCallPreserved s1 sm)
    ?_ ?_
  · states_from_pb_fetches_range_b b trapHooks 4556 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_vm_steps {
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      refine ⟨by simp [wp_norm, arm64_norm], ?_,
        by simp [v7_Saved4560Preserved, CryptoVerification.SpqrV1.States.FromPb.v7_Saved4560Preserved,
          AllocCallPreserved, wp_norm, arm64_norm, *]⟩
      simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)
    }
  · intro s2 hpc2 hrun2 hvm2 ⟨hpres2, hx25_2, hacp_12⟩
    rw [← A.pool_of_vmPreserved hvm2]
    have h4560 := v7_proto_decoder_dealloc_4560 hA s0 s2 (s0.sp - 2400#64) out ptsPtr ptsCap x28_val pts st
      (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
       ((pbA + 184#64) ↦₆₄ ptsCap) ∗
       ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       memRegion (pbA + 208#64) 16 ∗
       Frame)
      hfsp_align hpts_le hpts_cap_lt hpc2 hrun2 hpres2 hx25_2
    refine SepWP.mono h4560 ?_
    intro sf Pf _ _ ⟨evs, hevs, hPf, ⟨hsp_f, hx19_f, _, _, hx28_f, htr_f⟩, hacp_2f⟩
    refine ⟨evs, hevs, Entails.trans hPf ?_, hacp_12.trans hacp_2f, hsp_f, hx19_f, hx28_f, htr_f⟩
    have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
    have hhdr := protoPolyDecoderHeaders_entails_memRegion_40
      (pbA + 184#64) ptsCap ptsPtr (BitVec.ofNat 64 pts.length)
    have h192 : (pbA + 184#64) + 8#64 = pbA + 192#64 := by bv_omega
    have h200 : (pbA + 184#64) + 16#64 = pbA + 200#64 := by bv_omega
    have h208 : (pbA + 184#64) + 24#64 = pbA + 208#64 := by bv_omega
    rw [h192, h200, h208] at hhdr
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
        (((pbA + 184#64) ↦₆₄ ptsCap) ∗
         ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         memRegion (pbA + 208#64) 16) ∗
        (A.pool lim (M.stepEvents evs st) sf ∗ Frame) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hst (sepConj_mono_left hhdr)) (Entails.of_eq (by sep_ac_rfl))

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aBudget
