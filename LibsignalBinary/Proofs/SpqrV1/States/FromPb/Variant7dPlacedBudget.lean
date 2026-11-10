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
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7d
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7dPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part D

Lifts niche jump-table dispatch (`+36 -> +1056`), entry `ptsNeeded` validation (`+1056 -> +3480`),
and early error cleanup paths (`+1056 -> +4632` and `+3480 -> +4632`) to `VmPreserved` and
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7dPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_333 blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 ls_blockPlacement_base lsmpl withMemEq)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder PolynomialEncoder V1State pbToProtoPolyDecoder pbToProtoPolyEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.Drop
  (DropProtoUnchunkedCt1SentEkReceivedGhost cap_add_one_beq_zero_false dropStack32
   none2Cap_add_two_beq_zero noneCap_add_two_beq_zero protoUnchunkedCt1SentAt
   protoUnchunkedCt1SentEkReceivedAt protoUnchunkedCt1SentEkReceivedSize)
open CryptoVerification.SpqrV1.Poly (optProtoPolynomialEncoderAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved statesFromPbJumpTablePlacedAt v7_optDecoderCapProp
   v7_optProtoPolyDecoderTail v7_stackAt_dropStack32_to_encoderFromPbStack
   v7_stackAt_encoderFromPbStack_to_dropStack32)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
   RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (dropProtoUnchunkedCt1SentEkReceivedSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st sepWP_evs_nil seq_clean_evs)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (seq_clean_evs_lscl seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4PlacedBudget (v4_ptsCap_add_one_ne_zero)

/-! ## Re-exports of Pure Decomposition & `ptsNeeded` Helpers from `Variant7d` -/

abbrev v7_ct1SentToCt1SentEkReceived :=
  CryptoVerification.SpqrV1.States.FromPb.v7_ct1SentToCt1SentEkReceived
abbrev v7_optProtoUnchunkedCt1SentTail :=
  CryptoVerification.SpqrV1.States.FromPb.v7_optProtoUnchunkedCt1SentTail
abbrev v7_optUcCapProp := CryptoVerification.SpqrV1.States.FromPb.v7_optUcCapProp
abbrev v7_receivingEkPtsOk := CryptoVerification.SpqrV1.States.FromPb.v7_receivingEkPtsOk
abbrev v7_optProtoPolyDecoderTailWithoutPts :=
  CryptoVerification.SpqrV1.States.FromPb.v7_optProtoPolyDecoderTailWithoutPts

alias v7_protoUnchunkedCt1SentAt_eq :=
  CryptoVerification.SpqrV1.States.FromPb.v7_protoUnchunkedCt1SentAt_eq
alias v7_optUcCapProp_imp_or :=
  CryptoVerification.SpqrV1.States.FromPb.v7_optUcCapProp_imp_or
alias v7_optProtoUnchunkedCt1Sent_expose_w0 :=
  CryptoVerification.SpqrV1.States.FromPb.v7_optProtoUnchunkedCt1Sent_expose_w0
alias v7_optProtoUnchunkedCt1Sent_unexpose_some :=
  CryptoVerification.SpqrV1.States.FromPb.v7_optProtoUnchunkedCt1Sent_unexpose_some
alias v7_optProtoUnchunkedCt1Sent_unexpose_none :=
  CryptoVerification.SpqrV1.States.FromPb.v7_optProtoUnchunkedCt1Sent_unexpose_none
alias v7_optProtoPolyDecoderTail_expose_pts :=
  CryptoVerification.SpqrV1.States.FromPb.v7_optProtoPolyDecoderTail_expose_pts
alias v7_optProtoPolyDecoderTail_unexpose_pts :=
  CryptoVerification.SpqrV1.States.FromPb.v7_optProtoPolyDecoderTail_unexpose_pts
alias v7_ptsNeeded_sub_576_beq_zero :=
  CryptoVerification.SpqrV1.States.FromPb.v7_ptsNeeded_sub_576_beq_zero

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

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

/-! ## 1. Dispatch (`+36 -> +1056`) with `x9` -/

/-- `VmPreserved`-strengthened placed jump-table dispatch (`+36 -> +1056` in Block `333`) for the
    niche-encoded `Ct1Sampled` variant, additionally recording `sm.readReg64 .x9 = w0`. -/
theorem v7_dispatch_ct1Sampled_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA w0 : BitVec 64) (Rest : SepProp)
    (hw0 : w0 = noneCap ∨ w0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = out)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1056#64) s1
      ((pbA ↦₆₄ w0) ∗
        statesFromPbJumpTablePlacedAt ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢ (pbA ↦₆₄ w0) ∗ statesFromPbJumpTablePlacedAt ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = w0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x0 = pbA ∧
        sm.readReg64 .x25 = s0.sp - 608#64 ∧
        sm.readReg64 .x21 = s0.sp - 1008#64 ∧
        sm.readReg64 .x13 = s0.sp - 1136#64 ∧
        sm.readReg64 .x23 = s0.sp - 1552#64 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v7_dispatch_ct1Sampled_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA w0 Rest hw0
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx8_1) (by simpa using hx0_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx9_m, hx19_m, hx27_m, hx0_m, hx25_m, hx21_m, hx13_m, hx23_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx9_m, by simpa using hx19_m,
       by simpa using hx27_m, by simpa using hx0_m, by simpa using hx25_m,
       by simpa using hx21_m, by simpa using hx13_m, by simpa using hx23_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v7_dispatch_ct1Sampled_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA w0 : BitVec 64) (Rest : SepProp)
    (hw0 : w0 = noneCap ∨ w0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = out)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1056#64) s1
      ((pbA ↦₆₄ w0) ∗
        statesFromPbJumpTablePlacedAt ∗
        Rest ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢ (pbA ↦₆₄ w0) ∗ statesFromPbJumpTablePlacedAt ∗ Rest ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = w0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x0 = pbA ∧
        sm.readReg64 .x25 = s0.sp - 608#64 ∧
        sm.readReg64 .x21 = s0.sp - 1008#64 ∧
        sm.readReg64 .x13 = s0.sp - 1136#64 ∧
        sm.readReg64 .x23 = s0.sp - 1552#64 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v7_dispatch_ct1Sampled_placed (ext := ext)
    s0 s1 out pbA w0 (Rest ∗ A.pool lim st s1)
    hw0 hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-! ## 2. Entry `ptsNeeded` Check (`+1056 -> +3480` and `+1056 -> +4632`) -/

/-- `VmPreserved`-strengthened placed entry `ptsNeeded` check (`+1056 -> +3480`) when
    `v7_receivingEkPtsOk optDecPb` holds, preserving `x21`, `x23`, and `x25`. -/
theorem v7_entry_1056_to_3480_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA c1 w0 cap_dec x21_val x23_val x25_val : BitVec 64)
    (optDecPb : Option PolynomialDecoder) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec (optDecPb.map pbToProtoPolyDecoder))
    (hpts : v7_receivingEkPtsOk optDecPb)
    (hpc1 : s1.pc = lsmpl.base 333 + 1056#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx1_1 : s1.readReg64 .x1 = c1)
    (hx9_1 : s1.readReg64 .x9 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx25_1 : s1.readReg64 .x25 = x25_val)
    (hx26_1 : s1.readReg64 .x26 = s0.readReg64 .x0)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3480#64) s1
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder) ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x1 = c1 ∧
        sm.readReg64 .x9 = w0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x25 = x25_val ∧
        sm.readReg64 .x26 = s0.readReg64 .x0 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v7_entry_1056_to_3480_placed
      (A := A) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA c1 w0 cap_dec x21_val x23_val x25_val optDecPb Frame hcap_dec hpts
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx1_1) (by simpa using hx9_1) (by simpa using hx19_1)
      (by simpa using hx21_1) (by simpa using hx23_1) (by simpa using hx25_1)
      (by simpa using hx26_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx1_m, hx9_m, hx19_m, hx21_m, hx22_m, hx23_m, hx25_m, hx26_m, hx27_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx1_m, by simpa using hx9_m,
       by simpa using hx19_m, by simpa using hx21_m, by simpa using hx22_m,
       by simpa using hx23_m, by simpa using hx25_m, by simpa using hx26_m,
       by simpa using hx27_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v7_entry_1056_to_3480_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA c1 w0 cap_dec x21_val x23_val x25_val : BitVec 64)
    (optDecPb : Option PolynomialDecoder) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec (optDecPb.map pbToProtoPolyDecoder))
    (hpts : v7_receivingEkPtsOk optDecPb)
    (hpc1 : s1.pc = lsmpl.base 333 + 1056#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx1_1 : s1.readReg64 .x1 = c1)
    (hx9_1 : s1.readReg64 .x9 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx25_1 : s1.readReg64 .x25 = x25_val)
    (hx26_1 : s1.readReg64 .x26 = s0.readReg64 .x0)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3480#64) s1
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder) ∗
        Frame ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢
          ((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder) ∗
          Frame ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x1 = c1 ∧
        sm.readReg64 .x9 = w0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x25 = x25_val ∧
        sm.readReg64 .x26 = s0.readReg64 .x0 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v7_entry_1056_to_3480_placed (A := A.repAlloc) (ext := ext)
    s0 s1 out pbA c1 w0 cap_dec x21_val x23_val x25_val optDecPb (Frame ∗ A.pool lim st s1)
    hcap_dec hpts hpc1 hrun1 hsp1 hx1_1 hx9_1 hx19_1 hx21_1 hx23_1 hx25_1
    hx26_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- Budget-threaded placed helper for `+1092 -> +1096` (`bl` Block `286`): calls
    `drop_glue::<ProtoUnchunkedCt1SentEkReceived>` with `x0 = pbA` under `FreeOnlyEvs`. -/
theorem v7_call_drop_proto_unchunked_ct1_sent_1092_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1092#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1096#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        protoUnchunkedCt1SentEkReceivedAt A.repAlloc pbA (v7_ct1SentToCt1SentEkReceived u) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion pbA 128 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  refine SepWP.weaken_pre
    (sepConj_mono_left (v7_stackAt_encoderFromPbStack_to_dropStack32 (s0.sp - 2400#64))) ?_
  rw [h7552]
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 286)
    (P_mid := fun sm =>
      protoUnchunkedCt1SentEkReceivedAt A.repAlloc pbA (v7_ct1SentToCt1SentEkReceived u) ∗
      A.pool lim st sm ∗
      stackAt (s0.sp - 2400#64) dropStack32 ∗
      (memRegion (s0.sp - 7552#64) 1024 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x0 = pbA ∧
      sm.readReg64 .lr = (blkPl_333).base + 1096#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc1
    change s1.pc = (blkPl_333).base + 1092#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 286) s1 _ _
    wp_steps_sync_333 (lsmpl.base 286)
    try simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hlr_2, hx19_2, hx22_2, hx27_2, htr2⟩
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
    have hdrop :=
      Variant7aPlacedBudget.v7_sub_ok_drop_proto_unchunked_ct1_sent_ek_received_mem_placed hA hcl2
    simp only [withMemEq, dropProtoUnchunkedCt1SentEkReceivedSpec] at hdrop
    dsimp only [protoUnchunkedCt1SentEkReceivedSize, BitVec.ofNat_eq_ofNat] at hdrop ⊢
    rw [← ls_blockPlacement_base (i := 333)]
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 1096#64) s2 _ _
    rw [show stackAt (s0.sp - 2400#64) dropStack32 = stackAt s2.sp dropStack32 from hsp2 ▸ rfl]
    wp_call hdrop ((⟨pbA, v7_ct1SentToCt1SentEkReceived u⟩ : DropProtoUnchunkedCt1SentEkReceivedGhost), st)
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
      rw [h7552] at hst
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
          (memRegion pbA 128 ∗ A.pool lim (M.stepEvents w st) _ ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

/-- Budget-threaded placed bad `ptsNeeded` path (`+1056 -> +1080 -> +4528 -> +4632`):
    when `s.receivingEk = some d` and `(d.ptsNeeded == 576#32) = false`, drops `s.uc` (if `some`),
    sets `w28 = 2` (`.msgDecode`), drops `s.sendingCt1` and `s.receivingEk` via `+4528`,
    and reaches `+4632` with `memRegion pbA 224` under `FreeOnlyEvs`. -/
theorem v7_entry_bad_pts_1056_to_4632_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA w0 cap_dec : BitVec 64)
    (optUcPb : Option V1State.Unchunked.Ct1Sent)
    (optEncPb : Option PolynomialEncoder)
    (d : PolynomialDecoder) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hcap_uc : v7_optUcCapProp w0 optUcPb)
    (hcap_dec : v7_optDecoderCapProp cap_dec (some (pbToProtoPolyDecoder d)))
    (hpts : (d.ptsNeeded == 576#32) = false)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1056#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A.repAlloc pbA w0 optUcPb) ∗
        optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion pbA 224 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 2#64 ∧
        TraceCalleeSaved sm s0) := by
  refine seq_clean_evs_lscl hcl1
    (mid := lsmpl.base 333 + 4528#64)
    (P_evs := fun evs1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      (memRegion pbA 128 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = 2#64 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · have hne_dec := v4_ptsCap_add_one_ne_zero hcap_dec
    have hpts' : ((pbToProtoPolyDecoder d).ptsNeeded == 576#32) = false := hpts
    have hpts_sub := v7_ptsNeeded_sub_576_beq_zero hpts'
    refine SepWP.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d)) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A.repAlloc pbA w0 optUcPb) ∗
           optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
           ((pbA + 184#64) ↦₆₄ cap_dec) ∗
           A.pool lim st s1 ∗ Frame) by sep_ac_rfl))
        (sepConj_mono_left
          (v7_optProtoPolyDecoderTail_expose_pts A.repAlloc pbA cap_dec (pbToProtoPolyDecoder d)))) ?_
    cases optUcPb with
    | none =>
      unfold v7_optUcCapProp at hcap_uc
      subst hcap_uc
      dsimp only [v7_optProtoUnchunkedCt1SentTail,
        CryptoVerification.SpqrV1.States.FromPb.v7_optProtoUnchunkedCt1SentTail]
      dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx9_1 ⊢
      rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 1056#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4528#64) s1 _ _
      apply sepWP_evs_nil
      simp only [AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 4528#64)
      try simp only [State.setMem_setMem]
      refine entails_pre_st (fun _ hsc => ?_) ?_
      · subst hsc
        have hun_dec :=
          v7_optProtoPolyDecoderTail_unexpose_pts A.repAlloc pbA cap_dec (pbToProtoPolyDecoder d)
        have hun_uc := v7_optProtoUnchunkedCt1Sent_unexpose_none pbA
        dsimp only [noneCap] at hun_uc
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((pbA + 208#64) ↦₃₂ (pbToProtoPolyDecoder d).ptsNeeded) ∗
             v7_optProtoPolyDecoderTailWithoutPts A.repAlloc (pbA + 184#64) cap_dec (pbToProtoPolyDecoder d)) ∗
            ((pbA ↦₆₄ 18446744073709551615#64) ∗ memRegion (pbA + 8#64) 120) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
             ((pbA + 184#64) ↦₆₄ cap_dec) ∗
             A.pool lim st _ ∗ Frame) by sep_ac_rfl)) ?_
        exact Entails.trans
          (sepConj_mono hun_dec (sepConj_mono_left hun_uc))
          (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    | some u =>
      unfold v7_optUcCapProp at hcap_uc
      have hne_uc := cap_add_one_beq_zero_false hcap_uc
      refine seq_clean_lscl_st hcl1
        (mid := lsmpl.base 333 + 1092#64)
        (P_mid := fun sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          protoUnchunkedCt1SentEkReceivedAt A.repAlloc pbA (v7_ct1SentToCt1SentEkReceived u) ∗
          A.pool lim st sm ∗
          (optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
           Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = pbA ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x27 = pbA ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
        change s1.pc = (blkPl_333).base + 1056#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 1092#64) s1 _ _
        wp_steps_sync_333 ((blkPl_333).base + 1092#64)
        try simp only [State.setMem_setMem]
        refine entails_pre_st (fun _ hsc => ?_) ?_
        · subst hsc
          have hun_dec :=
            v7_optProtoPolyDecoderTail_unexpose_pts A.repAlloc pbA cap_dec (pbToProtoPolyDecoder d)
          have hun_uc := v7_optProtoUnchunkedCt1Sent_unexpose_some A.repAlloc pbA w0 u
          rw [v7_protoUnchunkedCt1SentAt_eq] at hun_uc
          refine Entails.trans
            (Entails.of_eq (show _ =
              (((pbA + 208#64) ↦₃₂ (pbToProtoPolyDecoder d).ptsNeeded) ∗
               v7_optProtoPolyDecoderTailWithoutPts A.repAlloc (pbA + 184#64) cap_dec (pbToProtoPolyDecoder d)) ∗
              ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A.repAlloc pbA w0 (some u)) ∗
              (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               A.pool lim st _ ∗
               optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
               ((pbA + 184#64) ↦₆₄ cap_dec) ∗
               Frame) by sep_ac_rfl)) ?_
          exact Entails.trans
            (sepConj_mono hun_dec (sepConj_mono_left hun_uc))
            (Entails.of_eq (by sep_ac_rfl))
        · wp_done
      · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx19_2, hx22_2, hx27_2, htr2⟩
        refine seq_clean_evs
          (mid := lsmpl.base 333 + 1096#64)
          (P_evs := fun evs1 sm =>
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion pbA 128 ∗
            A.pool lim (M.stepEvents evs1 st) sm ∗
            (optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
             (((pbA + 184#64) ↦₆₄ cap_dec) ∗
              v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
             Frame))
          (Q := fun sm =>
            sm.sp = s0.sp - 2400#64 ∧
            sm.readReg64 .x19 = out ∧
            sm.readReg64 .x22 = cap_dec ∧
            sm.readReg64 .x27 = pbA ∧
            TraceCalleeSaved sm s0)
          (v7_call_drop_proto_unchunked_ct1_sent_1092_placed hA s0 s2 out pbA cap_dec u st _
            hcl2 hsp0_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx27_2 htr2)
          ?_
        intro evs1 s3 hevs1 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
        rw [← ls_blockPlacement_base (i := 333)] at hpc3 ⊢
        change s3.pc = (blkPl_333).base + 1096#64 at hpc3
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4528#64) s3 _ _
        apply sepWP_with_evs evs1 hevs1
        wp_steps_sync_333 ((blkPl_333).base + 4528#64)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
  · intro evs1 s4 hevs1 hpc4 hrun4 hcl4 ⟨hsp4, hx19_4, hx22_4, hx27_4, hx28_4, htr4⟩
    have h4528 := Variant7bPlacedBudget.v7_cleanup_4528_placed hA s0 s4 out pbA cap_dec 2#64
      (optEncPb.map pbToProtoPolyEncoder) (some (pbToProtoPolyDecoder d))
      (M.stepEvents evs1 st) (memRegion pbA 128 ∗ Frame)
      hcl4 hcap_dec hsp0_align hpc4 hrun4 hsp4 hx19_4 hx22_4 hx27_4 hx28_4 htr4
    refine SepWP.mono h4528 fun sm Pm _ _ ⟨evs2, hevs2, hPm, hq⟩ => ?_
    refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hq⟩
    rw [AllocCostModel.stepEvents_append]
    refine Entails.trans hPm ?_
    have hm184 := ProofLib.memRegion_split pbA 128 56 (by decide)
    have hm224 := ProofLib.memRegion_split pbA 184 40 (by decide)
    rw [hm224, hm184]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. `<Ct1Sent>::from_pb` Phase (`+3480 -> +4632` Error Exit) -/

/-- Budget-threaded placed `s.uc = none` error path at `+3480 -> +4524 -> +4528 -> +4632`:
    when `w0 = noneCap` (`x9 = noneCap`), `+3480..+3484` branches to `+4524`, sets `w28 = 0`,
    and runs `v7_cleanup_4528_placed` to reach `+4632` with `memRegion pbA 224` under `FreeOnlyEvs`. -/
theorem v7_uc_none_3480_to_4632_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (optEncPb : Option PolynomialEncoder)
    (optDecPb : Option PolynomialDecoder) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hcap_dec : v7_optDecoderCapProp cap_dec (optDecPb.map pbToProtoPolyDecoder))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3480#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = noneCap)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((pbA ↦₆₄ noneCap) ∗ v7_optProtoUnchunkedCt1SentTail A.repAlloc pbA noneCap none) ∗
        optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder)) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion pbA 224 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 333 + 4528#64)
    (P_mid := fun sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder)) ∗
      A.pool lim st sm ∗
      (memRegion pbA 128 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = 0#64 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [v7_optProtoUnchunkedCt1SentTail,
        CryptoVerification.SpqrV1.States.FromPb.v7_optProtoUnchunkedCt1SentTail]
    dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx9_1 ⊢
    rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 3480#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4528#64) s1 _ _
    wp_steps_sync_333 ((blkPl_333).base + 4528#64)
    try simp only [State.setMem_setMem]
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      have hun_uc := v7_optProtoUnchunkedCt1Sent_unexpose_none pbA
      dsimp only [noneCap] at hun_uc
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((pbA ↦₆₄ 18446744073709551615#64) ∗ memRegion (pbA + 8#64) 120) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder)) ∗
           A.pool lim st _ ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hun_uc) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    refine SepWP.mono
      (Variant7bPlacedBudget.v7_cleanup_4528_placed hA s0 s2 out pbA cap_dec 0#64
        (optEncPb.map pbToProtoPolyEncoder) (optDecPb.map pbToProtoPolyDecoder)
        st (memRegion pbA 128 ∗ Frame)
        hcl2 hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2)
      ?_
    intro sm Pm _ _ ⟨evs, hevs, hPm, hq⟩
    refine ⟨evs, hevs, Entails.trans hPm ?_, hq⟩
    have hm184 := ProofLib.memRegion_split pbA 128 56 (by decide)
    have hm224 := ProofLib.memRegion_split pbA 184 40 (by decide)
    rw [hm224, hm184]
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7dPlacedBudget
