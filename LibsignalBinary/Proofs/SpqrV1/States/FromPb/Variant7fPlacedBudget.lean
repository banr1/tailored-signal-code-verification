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
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7f
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7fPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part F

Lifts `<Ct1Sent>::from_pb` setup and call (`+3480 -> +3548 -> lsmpl.base 339`), error cleanup
(`+3552 -> +5444 -> +4632`), and `Ok(uc)` spill/branching (`+3552 -> +7100 | +3652`) to
`VmPreserved` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7fPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 ls_blockPlacement_base lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (ProtoPolynomialDecoder ProtoPolynomialEncoder StatesError V1State)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.Drop
  (none2Cap_add_two_beq_zero noneCap_add_two_beq_zero protoUnchunkedCt1SentAt)
open CryptoVerification.SpqrV1.Poly (optProtoPolynomialEncoderAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved v7_1888_words_to_memRegion_128 v7_ct1SentResult_err_unpack
   v7_ct1SentWordsAt v7_optProtoUnchunkedCt1SentTail)
open CryptoVerification.SpqrV1.Unchunked
  (ct1SentResultAt extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (blk333_noSvc0 entails_pre_st seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bPlacedBudget
  (v7_cleanup_5444_placed v7_optDecoderCapProp v7_optProtoPolyDecoderTail)

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

/-! ## 1. `<Ct1Sent>::from_pb` Copy (`+3480 -> +3548`) -/

/-- `VmPreserved`-strengthened placed `<Ct1Sent>::from_pb` copy (`+3480 -> +3548`, Block `333`)
    when `w0.toNat < 2 ^ 63`. -/
theorem v7_copy_uc_3480_to_3548_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA w0 cap_dec x21_val x23_val x25_val : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) (Frame : SepProp)
    (hw0 : w0.toNat < 2 ^ 63)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3480#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx9_1 : s1.readReg64 .x9 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx25_1 : s1.readReg64 .x25 = x25_val)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3548#64) s1
      ((pbA ↦₆₄ w0) ∗
        v7_optProtoUnchunkedCt1SentTail A pbA w0 (some u) ∗
        memRegion (fsp + 240#64) 128 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          memRegion pbA 128 ∗
          protoUnchunkedCt1SentAt A (fsp + 240#64) u ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x25 = x25_val ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v7_copy_uc_3480_to_3548_placed
      (A := A) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out pbA w0 cap_dec x21_val x23_val x25_val u Frame hw0 hfsp_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx9_1) (by simpa using hx19_1) (by simpa using hx21_1)
      (by simpa using hx22_1) (by simpa using hx23_1) (by simpa using hx25_1)
      (by simpa using hx27_1) ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx23_m, hx25_m, hx27_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx19_m, by simpa using hx21_m, by simpa using hx22_m,
       by simpa using hx23_m, by simpa using hx25_m, by simpa using hx27_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v7_copy_uc_3480_to_3548_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA w0 cap_dec x21_val x23_val x25_val : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) (Frame : SepProp)
    (hw0 : w0.toNat < 2 ^ 63)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3480#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx9_1 : s1.readReg64 .x9 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx25_1 : s1.readReg64 .x25 = x25_val)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3548#64) s1
      ((pbA ↦₆₄ w0) ∗
        v7_optProtoUnchunkedCt1SentTail A.repAlloc pbA w0 (some u) ∗
        memRegion (fsp + 240#64) 128 ∗
        Frame ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢
          memRegion pbA 128 ∗
          protoUnchunkedCt1SentAt A.repAlloc (fsp + 240#64) u ∗
          Frame ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x25 = x25_val ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v7_copy_uc_3480_to_3548_placed (A := A.repAlloc) (ext := ext)
    s0 s1 fsp out pbA w0 cap_dec x21_val x23_val x25_val u (Frame ∗ A.pool lim st s1)
    hw0 hfsp_align hpc1 hrun1 hsp1 hx9_1 hx19_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-! ## 2. `<Ct1Sent>::from_pb` Branch-With-Link (`+3548 -> lsmpl.base 339`) -/

/-- `VmPreserved`-strengthened placed `bl` at `+3548` to `<spqr::v1::unchunked::states::Ct1Sent>::from_pb`
    (`lsmpl.base 339`), setting `x30 = lsmpl.base 333 + 3552`. -/
theorem v7_bl_ct1_sent_3548_to_15272_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_dec x21_val x23_val x25_val : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 3548#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = fsp + 1888#64)
    (hx1_1 : s1.readReg64 .x1 = fsp + 240#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx25_1 : s1.readReg64 .x25 = x25_val)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 339) s1
      P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x25 = x25_val ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 3552#64 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v7_bl_ct1_sent_3548_to_15272_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out pbA cap_dec x21_val x23_val x25_val P
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx0_1) (by simpa using hx1_1) (by simpa using hx19_1)
      (by simpa using hx21_1) (by simpa using hx22_1) (by simpa using hx23_1)
      (by simpa using hx25_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx23_m, hx25_m, hx27_m, hx30_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx19_m, by simpa using hx21_m, by simpa using hx22_m,
       by simpa using hx23_m, by simpa using hx25_m, by simpa using hx27_m,
       by simpa using hx30_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v7_bl_ct1_sent_3548_to_15272_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_dec x21_val x23_val x25_val : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 3548#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = fsp + 1888#64)
    (hx1_1 : s1.readReg64 .x1 = fsp + 240#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx25_1 : s1.readReg64 .x25 = x25_val)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 339) s1
      (P ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢ P ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x25 = x25_val ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 3552#64 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v7_bl_ct1_sent_3548_to_15272_placed (ext := ext)
    s0 s1 fsp out pbA cap_dec x21_val x23_val x25_val (P ∗ A.pool lim st s1)
    hpc1 hrun1 hsp1 hx0_1 hx1_1 hx19_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-! ## 3. `<Ct1Sent>::from_pb` Error Branch (`+3552 -> +5444 -> +4632`) -/

/-- Budget-threaded placed error branch at `+3552 -> +5444 -> +4632` when
    `<UnchunkedCt1Sent>::from_pb` returns `.error`, dropping `optEnc` and `optDec`
    under `FreeOnlyEvs`. -/
theorem v7_uc_err_3552_to_4632_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (e : StatesError)
    (optEnc : Option ProtoPolynomialEncoder)
    (optDec : Option ProtoPolynomialDecoder)
    (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
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
        ct1SentResultAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) (.error e) ∗
        optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) optEnc ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
          memRegion (pbA + 128#64) 56 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        (sm.readReg64 .x28).extractLsb' 0 8 = 0#8 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hpre :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ct1SentResultAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) (.error e) ∗
        optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) optEnc ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗ Frame ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64,
        ⌜w8.extractLsb' 0 8 = 0#8⌝ ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         ((s0.sp - 2400#64) + 1888#64) ↦₆₄ noneCap ∗
         ((s0.sp - 2400#64) + 1896#64) ↦₆₄ w8 ∗
         ((s0.sp - 2400#64) + 1904#64) ↦₆₄ w16 ∗
         ((s0.sp - 2400#64) + 1912#64) ↦₆₄ w24 ∗
         memRegion ((s0.sp - 2400#64) + 1920#64) 96 ∗
         optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) optEnc ∗
         (((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
         A.pool lim st s1 ∗ Frame) := by
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left
        (v7_ct1SentResult_err_unpack A.repAlloc (F := F) (s0.sp - 2400#64) e))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w8
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w24
    refine Entails.sepExists_right w8 (Entails.sepExists_right w16 (Entails.sepExists_right w24 ?_))
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w16
  apply ProofLib.SepWP.exists_left; intro w24
  apply ProofLib.SepWP.pure_elim; intro hw8
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 333 + 5444#64)
    (P_mid := fun sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) optEnc ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
      A.pool lim st sm ∗
      (memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = w8 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · have h1888 : (s0.sp - 2400#64) + 1888#64 = s0.sp - 512#64 := by bv_omega
    have h1896 : (s0.sp - 2400#64) + 1896#64 = s0.sp - 504#64 := by bv_omega
    have h1904 : (s0.sp - 2400#64) + 1904#64 = s0.sp - 496#64 := by bv_omega
    have h1912 : (s0.sp - 2400#64) + 1912#64 = s0.sp - 488#64 := by bv_omega
    have hjoin := v7_1888_words_to_memRegion_128 (s0.sp - 2400#64) noneCap w8 w16 w24
    rw [h1888, h1896, h1904, h1912] at hjoin ⊢
    dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 3552#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5444#64) s1 _ _
    wp_steps_sync_333 ((blkPl_333).base + 5444#64)
    try simp only [State.setMem_setMem]
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((s0.sp - 512#64) ↦₆₄ noneCap) ∗
           ((s0.sp - 504#64) ↦₆₄ w8) ∗
           ((s0.sp - 496#64) ↦₆₄ w16) ∗
           ((s0.sp - 488#64) ↦₆₄ w24) ∗
           memRegion ((s0.sp - 2400#64) + 1920#64) 96) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) optEnc ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
           A.pool lim st _ ∗ Frame) by dsimp only [noneCap, BitVec.ofNat_eq_ofNat]; sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hjoin) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    have h5444 := v7_cleanup_5444_placed hA s0 s2 out pbA cap_dec w8 optEnc optDec
      st (memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗ Frame)
      hcl2 hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
    refine SepWP.mono h5444 ?_
    intro sf Pf _ _ ⟨evs, hevs, hPf, hsp_f, hx19_f, hx28_f, htr_f⟩
    rw [hx28_f]
    exact ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
      hsp_f, hx19_f, hw8, htr_f⟩

/-! ## 4. `<Ct1Sent>::from_pb` `Ok` Unpack/Spill (`+3552 -> +3648`) and `sendingCt1 = none` (`+3648 -> +7100`) -/

/-- `VmPreserved`-strengthened spill of `Ok(uc)` from `fsp + 1888..2016` to `fsp + 1264..1392`
    and branch to `+7100` when `[pbA + 128] = noneCap` (`s.sendingCt1 = none`). -/
theorem v7_uc_ok_spill_3552_to_7100_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_dec : BitVec 64)
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hc1 : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7100#64) s1
      (v7_ct1SentWordsAt (fsp + 1888#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch ∗
        memRegion (fsp + 1264#64) 128 ∗
        ((pbA + 128#64) ↦₆₄ noneCap) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (fsp + 1888#64) 128 ∗
          v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch ∗
          ((pbA + 128#64) ↦₆₄ noneCap) ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x1 = c1 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = p1 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v7_uc_ok_spill_3552_to_7100_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out pbA cap_dec c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch Frame
      hfsp_align hc1
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx22_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx1_m, hx19_m, hx22_m, hx24_m, hx27_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx1_m, by simpa using hx19_m,
       by simpa using hx22_m, by simpa using hx24_m, by simpa using hx27_m,
       by simpa using hx28_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v7_uc_ok_spill_3552_to_7100_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_dec : BitVec 64)
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hc1 : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7100#64) s1
      (v7_ct1SentWordsAt (fsp + 1888#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch ∗
        memRegion (fsp + 1264#64) 128 ∗
        ((pbA + 128#64) ↦₆₄ noneCap) ∗
        Frame ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (fsp + 1888#64) 128 ∗
          v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch ∗
          ((pbA + 128#64) ↦₆₄ noneCap) ∗
          Frame ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x1 = c1 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = p1 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v7_uc_ok_spill_3552_to_7100_placed (ext := ext)
    s0 s1 fsp out pbA cap_dec c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch
    (Frame ∗ A.pool lim st s1)
    hfsp_align hc1 hpc1 hrun1 hsp1 hx19_1 hx22_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- `VmPreserved`-strengthened spill of `Ok(uc)` from `fsp + 1888..2016` to `fsp + 1264..1392`
    and fallthrough to `+3652` when `[pbA + 128] = cap_enc` with `cap_enc.toNat < 2 ^ 63`
    (`s.sendingCt1 = some enc`). -/
theorem v7_uc_ok_spill_3552_to_3652_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_enc cap_dec x21_val x23_val x25_val : BitVec 64)
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hc1 : c1.toNat < 2 ^ 63)
    (hcap_enc : cap_enc.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx25_1 : s1.readReg64 .x25 = x25_val)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3652#64) s1
      (v7_ct1SentWordsAt (fsp + 1888#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch ∗
        memRegion (fsp + 1264#64) 128 ∗
        ((pbA + 128#64) ↦₆₄ cap_enc) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (fsp + 1888#64) 128 ∗
          v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch ∗
          ((pbA + 128#64) ↦₆₄ cap_enc) ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x1 = c1 ∧
        sm.readReg64 .x8 = cap_enc ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = x25_val ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = p1 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v7_uc_ok_spill_3552_to_3652_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out pbA cap_enc cap_dec x21_val x23_val x25_val
      c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch Frame
      hfsp_align hc1 hcap_enc
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx21_1) (by simpa using hx22_1)
      (by simpa using hx23_1) (by simpa using hx25_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx1_m, hx8_m, hx19_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m,
       hx27_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx1_m, by simpa using hx8_m,
       by simpa using hx19_m, by simpa using hx21_m, by simpa using hx22_m,
       by simpa using hx23_m, by simpa using hx24_m, by simpa using hx25_m,
       by simpa using hx26_m, by simpa using hx27_m, by simpa using hx28_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v7_uc_ok_spill_3552_to_3652_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_enc cap_dec x21_val x23_val x25_val : BitVec 64)
    (c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hc1 : c1.toNat < 2 ^ 63)
    (hcap_enc : cap_enc.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx25_1 : s1.readReg64 .x25 = x25_val)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3652#64) s1
      (v7_ct1SentWordsAt (fsp + 1888#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch ∗
        memRegion (fsp + 1264#64) 128 ∗
        ((pbA + 128#64) ↦₆₄ cap_enc) ∗
        Frame ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (fsp + 1888#64) 128 ∗
          v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch ∗
          ((pbA + 128#64) ↦₆₄ cap_enc) ∗
          Frame ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x1 = c1 ∧
        sm.readReg64 .x8 = cap_enc ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = x25_val ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = p1 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v7_uc_ok_spill_3552_to_3652_placed (ext := ext)
    s0 s1 fsp out pbA cap_enc cap_dec x21_val x23_val x25_val
    c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 epoch
    (Frame ∗ A.pool lim st s1)
    hfsp_align hc1 hcap_enc hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7fPlacedBudget
