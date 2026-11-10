/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3Placed
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 2 (`HeaderSent`) — Part E3

Relocatable Block-`333` `receivingCt1` (`<PolyDecoder>::from_pb`) stage (`+9328..+9404`) and
`FreeOnlyEvs` error exits to `+9228` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl)
open CryptoVerification.LibsignalSpqrV1 (PolyEncoder PolynomialError spqrAuthApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop (unchunkedEkSentAt vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (polyEncoderAt resultPolyDecoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved v2hse3_1888_tag_392_to_memRegion_400 v2hse3_bv_add_add_lit
   v2hse3_resultPolyDecoder_err_entails_tag_392 v2hse3_x23_add_193_sext v2hse3_x25_add_65_sext)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget blk333_noSvc0 entails_pre_st seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdPlacedBudget
  (v2hsd_cleanup_11024_to_9228_of_dealloc_placed v2hsd_cleanup_11240_to_9228_of_dealloc_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v2hse3_bv_add_add_lit
  v2hse3_x23_add_193_sext
  v2hse3_x25_add_65_sext

@[local simp]
private theorem stripS_pstate (keep : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS keep s).pstate = s.pstate := rfl

private theorem blkPl_333_base [LibsignalPlacement] :
    (blkPl_333).base = lsmpl.base 333 := rfl

local macro "wp_steps_sync_333 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException _))
    blkLib_eq_333 blk333_noSvc0 (mid := $mid)
  intro _m_strip
  try rw [← blkPl_333_base]
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## `receivingCt1 = none` Branch (`+9328 -> +11024 -> +9228`) -/

/-- At `+9328` (`b.eq +11024`), when `s1.pstate = addsPState64 noneCap 1#64`
(`receivingCt1 = none`), takes `b.eq +11024`, drops `[Poly; 16]` at `fsp + 1400`,
deallocates `(ca1, pa1)`, `(ca2, pa2)`, `(ca3, pa3)`, sets `x23 = 0#64`, and reaches `+9228`
under `FreeOnlyEvs`. -/
theorem v2hse3_none_dec_9328_to_9228_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (enc : PolyEncoder) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9328#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 1392#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hpstate1 : s1.pstate = addsPState64 noneCap 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 333 + 11024#64)
    (P_mid := fun sm =>
      stackAt fsp encoderFromPbStack ∗
      polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
      ((fsp + 200#64) ↦₆₄ ca1) ∗
      ((fsp + 1272#64) ↦₆₄ pa1) ∗
      ((fsp + 232#64) ↦₆₄ ca2) ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
      vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
      vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
      A.pool lim st sm ∗ Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x23 = fsp + 1392#64 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [noneCap] at hpstate1 ⊢
    change s1.pc = (blkPl_333).base + 9328#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 11024#64) s1 _ _
    wp_simp_pre [sepConj_assoc]
    wp_steps_sync_333 ((blkPl_333).base + 11024#64)
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx23_2, hx26_2, htr2⟩
    exact v2hsd_cleanup_11024_to_9228_of_dealloc_placed hdealloc
      s0 s2 fsp out ca1 pa1 ca2 pa2 ca3 pa3 enc st Frame
      hcl2 hfsp_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2 htr2

theorem v2hse3_none_dec_9328_to_9228_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (enc : PolyEncoder) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9328#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 1392#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hpstate1 : s1.pstate = addsPState64 noneCap 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) :=
  v2hse3_none_dec_9328_to_9228_of_dealloc_placed hA.dealloc
    s0 s1 fsp out ca1 pa1 ca2 pa2 ca3 pa3 enc st Frame
    hcl1 hfsp_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 hpstate1 htr1

/-! ## Copy `ProtoPolynomialDecoder` (`+9328 -> +9384`) and Call `<PolyDecoder>::from_pb` (`+9384 -> lsmpl.base 376`) -/

/-- `VmPreserved`-strengthened `ProtoPolynomialDecoder` copy (`+9328 -> +9384`, Block `333`). -/
theorem v2hse3_copy_dec_9328_to_9384_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out x20_val x21_val ca3 x28_val d0 d8 d16 d24 d32 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hd0 : d0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 9328#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = x20_val)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (hpstate1 : s1.pstate = addsPState64 d0 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9384#64) s1
      (((fsp + 1040#64) ↦₆₄ d8) ∗
        ((fsp + 1048#64) ↦₆₄ d16) ∗
        ((fsp + 1056#64) ↦₆₄ d24) ∗
        ((fsp + 1064#64) ↦₆₄ d32) ∗
        memRegion (fsp + 1848#64) 40 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 1040#64) ↦₆₄ d8) ∗
          ((fsp + 1048#64) ↦₆₄ d16) ∗
          ((fsp + 1056#64) ↦₆₄ d24) ∗
          ((fsp + 1064#64) ↦₆₄ d32) ∗
          ((fsp + 1848#64) ↦₆₄ d0) ∗
          ((fsp + 1856#64) ↦₆₄ d8) ∗
          ((fsp + 1864#64) ↦₆₄ d16) ∗
          ((fsp + 1872#64) ↦₆₄ d24) ∗
          ((fsp + 1880#64) ↦₆₄ d32) ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1848#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = x20_val ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2hse3Placed.v2hse3_copy_dec_9328_to_9384_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out x20_val x21_val ca3 x28_val d0 d8 d16 d24 d32 Frame
      hfsp_align hd0
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx20_1) (by simpa using hx21_1)
      (by simpa using hx22_1) (by simpa using hx25_1) (by simpa using hx26_1)
      (by simpa using hx28_1) (by simpa using hpstate1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx20_m, hx21_m, hx22_m,
        hx23_m, hx25_m, hx26_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx19_m, by simpa using hx20_m, by simpa using hx21_m,
       by simpa using hx22_m, by simpa using hx23_m, by simpa using hx25_m,
       by simpa using hx26_m, by simpa using hx28_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v2hse3_copy_dec_9328_to_9384_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out x20_val x21_val ca3 x28_val d0 d8 d16 d24 d32 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hd0 : d0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 9328#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = x20_val)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (hpstate1 : s1.pstate = addsPState64 d0 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9384#64) s1
      (((fsp + 1040#64) ↦₆₄ d8) ∗
        ((fsp + 1048#64) ↦₆₄ d16) ∗
        ((fsp + 1056#64) ↦₆₄ d24) ∗
        ((fsp + 1064#64) ↦₆₄ d32) ∗
        memRegion (fsp + 1848#64) 40 ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 1040#64) ↦₆₄ d8) ∗
          ((fsp + 1048#64) ↦₆₄ d16) ∗
          ((fsp + 1056#64) ↦₆₄ d24) ∗
          ((fsp + 1064#64) ↦₆₄ d32) ∗
          ((fsp + 1848#64) ↦₆₄ d0) ∗
          ((fsp + 1856#64) ↦₆₄ d8) ∗
          ((fsp + 1864#64) ↦₆₄ d16) ∗
          ((fsp + 1872#64) ↦₆₄ d24) ∗
          ((fsp + 1880#64) ↦₆₄ d32) ∗
          A.pool lim st sm ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1848#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = x20_val ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v2hse3_copy_dec_9328_to_9384_placed (ext := ext)
    s0 s1 fsp out x20_val x21_val ca3 x28_val d0 d8 d16 d24 d32
    (A.pool lim st s1 ∗ Frame)
    hfsp_align hd0 hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hx25_1 hx26_1 hx28_1 hpstate1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- `VmPreserved`-strengthened `bl <PolyDecoder>::from_pb` step at `+9384` to `lsmpl.base 376`. -/
theorem v2hse3_bl_decoder_9384_to_35448_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out x20_val x21_val ca3 x28_val : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 9384#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = fsp + 1888#64)
    (hx1_1 : s1.readReg64 .x1 = fsp + 1848#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = x20_val)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = fsp + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376) s1 P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1848#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = x20_val ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = x28_val ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 9388#64 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2hse3Placed.v2hse3_bl_decoder_9384_to_35448_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out x20_val x21_val ca3 x28_val P
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx0_1) (by simpa using hx1_1) (by simpa using hx19_1)
      (by simpa using hx20_1) (by simpa using hx21_1) (by simpa using hx22_1)
      (by simpa using hx23_1) (by simpa using hx25_1) (by simpa using hx26_1)
      (by simpa using hx28_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx20_m, hx21_m, hx22_m,
        hx23_m, hx25_m, hx26_m, hx28_m, hx30_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx19_m, by simpa using hx20_m, by simpa using hx21_m,
       by simpa using hx22_m, by simpa using hx23_m, by simpa using hx25_m,
       by simpa using hx26_m, by simpa using hx28_m, by simpa using hx30_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v2hse3_bl_decoder_9384_to_35448_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out x20_val x21_val ca3 x28_val : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 9384#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = fsp + 1888#64)
    (hx1_1 : s1.readReg64 .x1 = fsp + 1848#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = x20_val)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = fsp + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376) s1 (P ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢ P ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1848#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = x20_val ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = x28_val ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 9388#64 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v2hse3_bl_decoder_9384_to_35448_placed (ext := ext)
    s0 s1 fsp out x20_val x21_val ca3 x28_val (P ∗ A.pool lim st s1)
    hpc1 hrun1 hsp1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx26_1 hx28_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-! ## `<PolyDecoder>::from_pb` Return Branches (`+9388 -> +9228` on `Err`, `+9388 -> +9404` on `Ok`) -/

/-- At `+9388`, when `resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err)` holds,
loads `noneCap` from `[sp, #0x760]`, stores `noneCap` to `[sp, #0xd8]` (`fsp + 216#64`),
takes `b.eq +11240`, drops `enc` at `fsp + 1392` and `uc` at `fsp + 1264` via
`v2hsd_cleanup_11240_to_9228_of_dealloc_placed`, and reaches `+9228` under `FreeOnlyEvs`. -/
theorem v2hse3_err_dec_9388_to_9228_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out w216_old : BitVec 64)
    (enc : PolyEncoder)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSent (spqrAuthApi F))
    (err : PolynomialError) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9388#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err) ∗
        ((fsp + 216#64) ↦₆₄ w216_old) ∗
        polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
        unchunkedEkSentAt A.repAlloc (fsp + 1264#64) uc ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 216#64) ↦₆₄ noneCap) ∗
          memRegion (fsp + 1392#64) 400 ∗
          memRegion (fsp + 1264#64) 80 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left
      (v2hse3_resultPolyDecoder_err_entails_tag_392 A.repAlloc fsp err))) ?_
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 333 + 11240#64)
    (P_mid := fun sm =>
      stackAt fsp encoderFromPbStack ∗
      polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
      unchunkedEkSentAt A.repAlloc (fsp + 1264#64) uc ∗
      A.pool lim st sm ∗
      (memRegion (fsp + 1888#64) 400 ∗
       ((fsp + 216#64) ↦₆₄ noneCap) ∗
       Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [noneCap] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 9388#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 11240#64) s1 _ _
    wp_simp_pre [sepConj_assoc]
    wp_steps_sync_333 ((blkPl_333).base + 11240#64)
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      have hm400 := v2hse3_1888_tag_392_to_memRegion_400 fsp 18446744073709551615#64
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 1888#64) ↦₆₄ 18446744073709551615#64) ∗
         memRegion (fsp + 1896#64) 392) ∗
        (stackAt fsp encoderFromPbStack ∗
         polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
         unchunkedEkSentAt A.repAlloc (fsp + 1264#64) uc ∗
         A.pool lim st sc ∗
         (((fsp + 216#64) ↦₆₄ 18446744073709551615#64) ∗ Frame)) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hm400) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, htr2⟩
    have h11240 := v2hsd_cleanup_11240_to_9228_of_dealloc_placed hdealloc s0 s2 fsp out enc uc st
      (memRegion (fsp + 1888#64) 400 ∗ ((fsp + 216#64) ↦₆₄ noneCap) ∗ Frame)
      hcl2 hfsp_align hpc2 hrun2 hsp2 hx19_2 htr2
    exact SepWP.mono h11240 fun sm _Pm _ _ ⟨evs, hevs, hPm, hq⟩ =>
      ⟨evs, hevs, Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hq⟩

theorem v2hse3_err_dec_9388_to_9228_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out w216_old : BitVec 64)
    (enc : PolyEncoder)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSent (spqrAuthApi F))
    (err : PolynomialError) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9388#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err) ∗
        ((fsp + 216#64) ↦₆₄ w216_old) ∗
        polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
        unchunkedEkSentAt A.repAlloc (fsp + 1264#64) uc ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 216#64) ↦₆₄ noneCap) ∗
          memRegion (fsp + 1392#64) 400 ∗
          memRegion (fsp + 1264#64) 80 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) :=
  v2hse3_err_dec_9388_to_9228_of_dealloc_placed hA.dealloc
    s0 s1 fsp out w216_old enc uc err st Frame
    hcl1 hfsp_align hpc1 hrun1 hsp1 hx19_1 htr1

/-- `VmPreserved`-strengthened `<PolyDecoder>::from_pb = Ok` fallthrough (`+9388 -> +9404`). -/
theorem v2hse3_ok_dec_9388_to_9404_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out x20_val x21_val ca3 x28_val dw0 w216_old : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hdw0 : dw0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 9388#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = x20_val)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = fsp + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9404#64) s1
      (((fsp + 1888#64) ↦₆₄ dw0) ∗
        ((fsp + 216#64) ↦₆₄ w216_old) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 1888#64) ↦₆₄ dw0) ∗
          ((fsp + 216#64) ↦₆₄ dw0) ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x8 = dw0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = x20_val ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2hse3Placed.v2hse3_ok_dec_9388_to_9404_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out x20_val x21_val ca3 x28_val dw0 w216_old Frame
      hfsp_align hdw0
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx20_1) (by simpa using hx21_1)
      (by simpa using hx22_1) (by simpa using hx23_1) (by simpa using hx25_1)
      (by simpa using hx26_1) (by simpa using hx28_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx8_m, hx19_m, hx20_m, hx21_m, hx22_m,
        hx23_m, hx25_m, hx26_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx8_m, by simpa using hx19_m,
       by simpa using hx20_m, by simpa using hx21_m, by simpa using hx22_m,
       by simpa using hx23_m, by simpa using hx25_m, by simpa using hx26_m,
       by simpa using hx28_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v2hse3_ok_dec_9388_to_9404_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out x20_val x21_val ca3 x28_val dw0 w216_old : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hdw0 : dw0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 9388#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = x20_val)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = fsp + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9404#64) s1
      (((fsp + 1888#64) ↦₆₄ dw0) ∗
        ((fsp + 216#64) ↦₆₄ w216_old) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 1888#64) ↦₆₄ dw0) ∗
          ((fsp + 216#64) ↦₆₄ dw0) ∗
          A.pool lim st sm ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x8 = dw0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = x20_val ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v2hse3_ok_dec_9388_to_9404_placed (ext := ext)
    s0 s1 fsp out x20_val x21_val ca3 x28_val dw0 w216_old (A.pool lim st s1 ∗ Frame)
    hfsp_align hdw0 hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx26_1 hx28_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3PlacedBudget
