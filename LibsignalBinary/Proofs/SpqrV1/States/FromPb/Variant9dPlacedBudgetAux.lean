/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Auxiliary Stepping and Sequencer Lemmas for `Variant9dPlacedBudget`

Relocatable Block `330` `<Authenticator>::from_pb` contracts, `VmPreserved`-strengthened Variant 9
steps (`+2864 -> lsmpl.base 376`, `+3044 -> +8588 | +8180`), and `+7084` error-exit sequencers under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement blkLib_eq_333 blkPC_330 blkPC_333 blkPl_330 blkPl_333
   lsProg_330 lsProg_333 ls_blockPlacement_base ls_subroutine_ok_of_block lsmpl lsρ
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (Error PolynomialDecoder PolynomialError pbToProtoPolyDecoder)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly (protoPolynomialDecoderAt resultPolyDecoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (encoderFromPbStack loByte loBytes7 unshiftWord)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt spqrErrorByte statesFromPbSavedCells statesFromPbStack
   v9_decCellsAt v9_midQ128 v9_optProtoPolyDecoderHeap v9_optProtoPolyDecoderWordsAt
   v9_optProtoUcWordsAt v9_quadAt v9_wordAt)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
  (authFromPbPinnedSpec auth_from_pb_pinned_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (seq_clean_evs seq_clean_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlacedBudgetAux
  (v9_states_from_pb_err_7084_placed_budget)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

@[local simp]
private theorem stripS_readReg32 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (ProofLib.stripS keep s).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

/-! ## 1. Budget-Threaded Callee Contract for `Authenticator::from_pb` (Block `330`) -/

/-- Relocatable Block-`330` `<Authenticator>::from_pb` contract under explicit `subroutine_ok`
    hypotheses on `__rust_no_alloc_shim_is_unstable_v2`, `__rust_alloc`, and `memcpy`. -/
theorem v9_auth_from_pb_pinned_placed_ok_of_sub [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_330).rebase (blkPl_330).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_330).rebase (blkPl_330).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmc : subroutine_ok ((blkPC_330).rebase (blkPl_330).base (Rust.withPanics ext))
      (lsρ "memcpy") allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_330).rebase (blkPl_330).base (Rust.withPanics ext))
      (blkPl_330).base (authFromPbPinnedSpec M A lim) :=
  auth_from_pb_pinned_placed_ok hshim halloc hmc

/-- Relocatable Block-`330` `<Authenticator>::from_pb` contract under `FromPbAllocHooksBudget`. -/
theorem v9_auth_from_pb_pinned_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok ((blkPC_330).rebase (blkPl_330).base (Rust.withPanics ext))
      (blkPl_330).base (authFromPbPinnedSpec M A lim) :=
  v9_auth_from_pb_pinned_placed_ok_of_sub
    (spqr_hook_ok_of_mem hA.shim)
    (spqr_hook_ok_of_mem hA.alloc)
    (spqr_hook_ok_of_mem hA.memcpy)

/-- Cross-block `withLsCodeLoaded` lift of `v9_auth_from_pb_pinned_placed_ok` to any
    libsignal block `callerProg` (`idx < 619`). -/
theorem v9_auth_from_pb_pinned_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hA : FromPbAllocHooksBudget M A lim ext) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 330)
      (withLsCodeLoaded lsmpl (authFromPbPinnedSpec M A lim)) := by
  have hcl330 : subroutine_ok (lsProg_330 (Rust.withPanics ext)) (lsmpl.base 330)
      (withLsCodeLoaded lsmpl (authFromPbPinnedSpec M A lim)) := by
    rw [← ls_blockPlacement_base (i := 330)]
    exact subroutine_ok_withLsCodeLoaded_of_plain (v9_auth_from_pb_pinned_placed_ok hA)
  exact ls_subroutine_ok_of_block hcl330 hidx

/-! ## 2. `VmPreserved` & Pool-Threading Stepping Lemmas (`+2864 -> lsmpl.base 376`, `+3044 -> +8588 | +8180`) -/

/-- `VmPreserved`-strengthened step `+2864 -> lsmpl.base 376` when `ct1SentFromPb` returned
    `Ok(uc)` (`rkCap.toNat < 2 ^ 63`) and `receivingEk = some d` (`decW0.toNat < 2 ^ 63`). -/
theorem v9_step_2864_ok_some_to_3040_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep : BitVec 64)
    (decW0 decW8 decW16 : BitVec 64) (decD24 decD28 : BitVec 32)
    (decW32 : BitVec 64) (d : PolynomialDecoder)
    (w40 w48 w56 w72 w80 w128 w136 w144 w152 w200 w216 w240 w248 : BitVec 64)
    (d96 : BitVec 32) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hrk_lt : rkCap.toNat < 2 ^ 63) (hdec_lt : decW0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2864#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = decW8) (hx21 : s.readReg64 .x21 = decW0)
    (hx23 : s.readReg64 .x23 = decW32)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx27 : s.readReg64 .x27 = pbA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376) s
      (((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        ((fsp + 72#64) ↦₆₄ w72) ∗ ((fsp + 80#64) ↦₆₄ w80) ∗ ((fsp + 96#64) ↦₃₂ d96) ∗
        ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗ ((fsp + 144#64) ↦₆₄ w144) ∗
        ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
        ((fsp + 240#64) ↦₆₄ w240) ∗ ((fsp + 248#64) ↦ₛ loBytes7 w248) ∗
        memRegion (fsp + 896#64) 40 ∗
        v9_optProtoUcWordsAt (fsp + 1888#64) rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) decW0 decW8 decW16 decD24 decD28 decW32 ∗
        v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d))
          decW0 decW8 decW16 decD24 decD28 decW32 ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ protoPolynomialDecoderAt A (fsp + 896#64) (pbToProtoPolyDecoder d) ∗
          memRegion (fsp + 1888#64) 128 ∗
          ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
          ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
          ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
          ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte ep))) ∗
          ((fsp + 247#64) ↦₆₄ ep) ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) decW0 decW8 decW16 decD24 decD28 decW32 ∗
          Rest) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x0 = fsp + 1888#64 ∧ s1.readReg64 .x1 = fsp + 896#64 ∧
        s1.readReg64 .x19 = out ∧ s1.readReg64 .x21 = fsp + 848#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = esLen ∧
        s1.readReg64 .x26 = rkLen ∧ s1.readReg64 .x28 = rkPtr ∧
        s1.readReg64 .x30 = lsmpl.base 333 + 3044#64 ∧
        TraceCalleeSaved s1 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant9dPlaced.v9_step_2864_ok_some_to_3040_placed
      (A := A) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out pbA rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep
      decW0 decW8 decW16 decD24 decD28 decW32 d
      w40 w48 w56 w72 w80 w128 w136 w144 w152 w200 w216 w240 w248 d96 Rest
      hfsp_align hrk_lt hdec_lt
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx21)
      (by simpa using hx23) (by simpa using hx25) (by simpa using hx27)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s1 P1 hvm ⟨hP1, hsp1, hx0_1, hx1_1, hx19_1, hx21_1, hx24_1, hx25_1, hx26_1, hx28_1, hx30_1, htr1⟩ =>
      ⟨hP1, hvm, by simpa using hsp1, by simpa using hx0_1, by simpa using hx1_1,
       by simpa using hx19_1, by simpa using hx21_1, by simpa using hx24_1,
       by simpa using hx25_1, by simpa using hx26_1, by simpa using hx28_1,
       by simpa using hx30_1, ⟨by simpa using htr1.1, by simpa using htr1.2⟩⟩

theorem v9_step_2864_ok_some_to_3040_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep : BitVec 64)
    (decW0 decW8 decW16 : BitVec 64) (decD24 decD28 : BitVec 32)
    (decW32 : BitVec 64) (d : PolynomialDecoder)
    (w40 w48 w56 w72 w80 w128 w136 w144 w152 w200 w216 w240 w248 : BitVec 64)
    (d96 : BitVec 32) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hrk_lt : rkCap.toNat < 2 ^ 63) (hdec_lt : decW0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2864#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = decW8) (hx21 : s.readReg64 .x21 = decW0)
    (hx23 : s.readReg64 .x23 = decW32)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx27 : s.readReg64 .x27 = pbA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376) s
      (((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        ((fsp + 72#64) ↦₆₄ w72) ∗ ((fsp + 80#64) ↦₆₄ w80) ∗ ((fsp + 96#64) ↦₃₂ d96) ∗
        ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗ ((fsp + 144#64) ↦₆₄ w144) ∗
        ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
        ((fsp + 240#64) ↦₆₄ w240) ∗ ((fsp + 248#64) ↦ₛ loBytes7 w248) ∗
        memRegion (fsp + 896#64) 40 ∗
        v9_optProtoUcWordsAt (fsp + 1888#64) rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) decW0 decW8 decW16 decD24 decD28 decW32 ∗
        v9_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d))
          decW0 decW8 decW16 decD24 decD28 decW32 ∗ Rest ∗ A.pool lim st s)
      (fun s1 P1 =>
        (P1 ⊢ protoPolynomialDecoderAt A.repAlloc (fsp + 896#64) (pbToProtoPolyDecoder d) ∗
          memRegion (fsp + 1888#64) 128 ∗
          ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
          ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
          ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
          ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte ep))) ∗
          ((fsp + 247#64) ↦₆₄ ep) ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) decW0 decW8 decW16 decD24 decD28 decW32 ∗
          Rest ∗ A.pool lim st s1) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x0 = fsp + 1888#64 ∧ s1.readReg64 .x1 = fsp + 896#64 ∧
        s1.readReg64 .x19 = out ∧ s1.readReg64 .x21 = fsp + 848#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = esLen ∧
        s1.readReg64 .x26 = rkLen ∧ s1.readReg64 .x28 = rkPtr ∧
        s1.readReg64 .x30 = lsmpl.base 333 + 3044#64 ∧
        TraceCalleeSaved s1 s0) := by
  have hwp := v9_step_2864_ok_some_to_3040_placed (A := A.repAlloc) (ext := ext)
    s0 s fsp out pbA rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
    esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep
    decW0 decW8 decW16 decD24 decD28 decW32 d
    w40 w48 w56 w72 w80 w128 w136 w144 w152 w200 w216 w240 w248 d96
    (Rest ∗ A.pool lim st s)
    hfsp_align hrk_lt hdec_lt hpc hrun hsp hx19 hx20 hx21 hx23 hx25 hx27 htr
  refine SepWP.mono hwp fun s1 P1 _ _ ⟨hP1, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP1
  exact ⟨Entails.trans hP1 (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened error-branch step `+3044 -> +8588` when
    `decoderFromPbResult pbDec = .error err`. -/
theorem v9_step_3044_err_to_8588_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out rkPtr : BitVec 64) (err : PolynomialError) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 3044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8588#64) s
      (resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error err) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ memRegion (fsp + 1888#64) 400 ∗ Rest) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x28 = rkPtr ∧
        TraceCalleeSaved s1 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant9dPlaced.v9_step_3044_err_to_8588_placed
      (A := A) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out rkPtr err Rest hfsp_align
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx28)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s1 P1 hvm ⟨hP1, hsp1, hx19_1, hx28_1, htr1⟩ =>
      ⟨hP1, hvm, by simpa using hsp1, by simpa using hx19_1, by simpa using hx28_1,
       ⟨by simpa using htr1.1, by simpa using htr1.2⟩⟩

theorem v9_step_3044_err_to_8588_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out rkPtr : BitVec 64) (err : PolynomialError) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 3044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8588#64) s
      (resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err) ∗ Rest ∗ A.pool lim st s)
      (fun s1 P1 =>
        (P1 ⊢ memRegion (fsp + 1888#64) 400 ∗ Rest ∗ A.pool lim st s1) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x28 = rkPtr ∧
        TraceCalleeSaved s1 s0) := by
  have hwp := v9_step_3044_err_to_8588_placed (A := A.repAlloc) (ext := ext)
    s0 s fsp out rkPtr err (Rest ∗ A.pool lim st s)
    hfsp_align hpc hrun hsp hx19 hx28 htr
  refine SepWP.mono hwp fun s1 P1 _ _ ⟨hP1, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP1
  exact ⟨Entails.trans hP1 (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened ok-branch step `+3044 -> +8180` when
    `decoderFromPbResult pbDec = .ok dec` (`(v9_wordAt bs 0).toNat < 2 ^ 63`). -/
theorem v9_step_3044_ok_to_8180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s0 s : State) (fsp out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep : BitVec 64)
    (w104 w112 w120 w160 w192 w208 w224 w232 w832 w864 w880 w888 w2272 w2280 : BitVec 64)
    (d172 : BitVec 32)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848 : BitVec 128)
    (bs : List (BitVec 8)) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hw0_lt : (v9_wordAt bs 0).toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 3044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = fsp + 848#64) (hx24 : s.readReg64 .x24 = fsp + 1888#64)
    (hx25 : s.readReg64 .x25 = esLen) (hx26 : s.readReg64 .x26 = rkLen)
    (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s
      (((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
        ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
        ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗ ((fsp + 172#64) ↦₃₂ d172) ∗
        ((fsp + 192#64) ↦₆₄ w192) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
        ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte ep))) ∗
        ((fsp + 247#64) ↦₆₄ ep) ∗
        ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗ ((fsp + 640#64) ↦₁₂₈ q640) ∗
        ((fsp + 656#64) ↦₁₂₈ q656) ∗ ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
        ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗ ((fsp + 736#64) ↦₁₂₈ q736) ∗
        ((fsp + 752#64) ↦₁₂₈ q752) ∗ ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
        ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗ ((fsp + 832#64) ↦₆₄ w832) ∗
        ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ loBytes7 w864) ∗
        ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ loBytes7 w888) ∗
        v9_decCellsAt (fsp + 1888#64) bs ∗ ((fsp + 2272#64) ↦₆₄ w2272) ∗
        ((fsp + 2280#64) ↦₆₄ w2280) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
          ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
          ((fsp + 104#64) ↦₆₄ v9_wordAt bs 376) ∗ ((fsp + 112#64) ↦₆₄ w2272) ∗
          ((fsp + 120#64) ↦₆₄ w2280) ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
          ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 160#64) ↦₆₄ v9_wordAt bs 312) ∗
          ((fsp + 172#64) ↦₃₂ (loByte (v9_wordAt bs 8)).zeroExtend 32) ∗
          ((fsp + 192#64) ↦₆₄ v9_wordAt bs 360) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 208#64) ↦₆₄ rkPtr) ∗
          ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ v9_wordAt bs 344) ∗
          ((fsp + 232#64) ↦₆₄ v9_wordAt bs 296) ∗
          ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte ep))) ∗
          ((fsp + 247#64) ↦₆₄ ep) ∗
          ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs 48) ∗
          ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs 80) ∗
          ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs 112) ∗
          ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs 144) ∗
          ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs 176) ∗
          ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs 208) ∗
          ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs 240) ∗
          ((fsp + 832#64) ↦₆₄ v9_wordAt bs 256) ∗
          ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)) ∗
          ((fsp + 864#64) ↦ₛ loBytes7 (v9_wordAt bs 24 >>> 8)) ∗
          ((fsp + 880#64) ↦₆₄ unshiftWord ct1Len (loByte ep)) ∗
          ((fsp + 888#64) ↦ₛ loBytes7 (ep >>> 8)) ∗
          v9_decCellsAt (fsp + 1888#64) bs ∗ ((fsp + 2272#64) ↦₆₄ w2272) ∗
          ((fsp + 2280#64) ↦₆₄ w2280) ∗ Rest) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x0 = esPtr ∧ s1.readReg64 .x1 = v9_wordAt bs 336 ∧
        s1.readReg64 .x2 = v9_wordAt bs 264 ∧ s1.readReg32 .x3 = esLen.extractLsb' 0 32 ∧
        s1.readReg64 .x4 = ct1Cap ∧ s1.readReg64 .x5 = ct1Ptr ∧ s1.readReg64 .x6 = fsp + 576#64 ∧
        s1.readReg64 .x7 = v9_wordAt bs 0 ∧ s1.readReg64 .x8 = 11#64 ∧ s1.readReg64 .x9 = hdrCap ∧
        s1.readReg64 .x10 = v9_wordAt bs 304 ∧ s1.readReg64 .x11 = v9_wordAt bs 272 ∧
        s1.readReg64 .x12 = v9_wordAt bs 328 ∧ s1.readReg64 .x13 = mkCap ∧
        s1.readReg64 .x14 = hdrPtr ∧ s1.readReg64 .x15 = rkCap ∧
        s1.readReg64 .x16 = v9_wordAt bs 368 ∧ s1.readReg64 .x17 = esCap ∧
        s1.readReg64 .x18 = hdrLen ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x20 = rkLen ∧
        s1.readReg32 .x21 = (loByte ct1Len).zeroExtend 32 ∧
        s1.readReg64 .x22 = v9_wordAt bs 280 ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x24 = v9_wordAt bs 288 ∧ s1.readReg64 .x25 = mkPtr ∧
        s1.readReg64 .x26 = v9_wordAt bs 320 ∧ s1.readReg64 .x27 = esLen >>> 8 ∧
        s1.readReg32 .x27 = (esLen >>> 8).extractLsb' 0 32 ∧
        s1.readReg64 .x28 = v9_wordAt bs 352 ∧ s1.readReg64 .x30 = mkLen ∧
        TraceCalleeSaved s1 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant9dPlaced.v9_step_3044_ok_to_8180_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep
      w104 w112 w120 w160 w192 w208 w224 w232 w832 w864 w880 w888 w2272 w2280 d172
      q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848 bs Rest
      hfsp_align hw0_lt
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx21) (by simpa using hx24)
      (by simpa using hx25) (by simpa using hx26) (by simpa using hx28)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s1 P1 hvm ⟨hP1, hsp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1,
      hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx18_1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx27_32_1,
      hx28_1, hx30_1, htr1⟩ =>
      ⟨hP1, hvm, by simpa using hsp1, by simpa using hx0_1, by simpa using hx1_1,
       by simpa using hx2_1, by simpa using hx3_1, by simpa using hx4_1, by simpa using hx5_1,
       by simpa using hx6_1, by simpa using hx7_1, by simpa using hx8_1, by simpa using hx9_1,
       by simpa using hx10_1, by simpa using hx11_1, by simpa using hx12_1, by simpa using hx13_1,
       by simpa using hx14_1, by simpa using hx15_1, by simpa using hx16_1, by simpa using hx17_1,
       by simpa using hx18_1, by simpa using hx19_1, by simpa using hx20_1, by simpa using hx21_1,
       by simpa using hx22_1, by simpa using hx23_1, by simpa using hx24_1, by simpa using hx25_1,
       by simpa using hx26_1, by simpa using hx27_1, by simpa using hx27_32_1,
       by simpa using hx28_1, by simpa using hx30_1,
       ⟨by simpa using htr1.1, by simpa using htr1.2⟩⟩

theorem v9_step_3044_ok_to_8180_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)} (s0 s : State) (fsp out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep : BitVec 64)
    (w104 w112 w120 w160 w192 w208 w224 w232 w832 w864 w880 w888 w2272 w2280 : BitVec 64)
    (d172 : BitVec 32)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848 : BitVec 128)
    (bs : List (BitVec 8)) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hw0_lt : (v9_wordAt bs 0).toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 3044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = fsp + 848#64) (hx24 : s.readReg64 .x24 = fsp + 1888#64)
    (hx25 : s.readReg64 .x25 = esLen) (hx26 : s.readReg64 .x26 = rkLen)
    (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s
      (((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
        ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
        ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗ ((fsp + 172#64) ↦₃₂ d172) ∗
        ((fsp + 192#64) ↦₆₄ w192) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
        ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte ep))) ∗
        ((fsp + 247#64) ↦₆₄ ep) ∗
        ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗ ((fsp + 640#64) ↦₁₂₈ q640) ∗
        ((fsp + 656#64) ↦₁₂₈ q656) ∗ ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
        ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗ ((fsp + 736#64) ↦₁₂₈ q736) ∗
        ((fsp + 752#64) ↦₁₂₈ q752) ∗ ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
        ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗ ((fsp + 832#64) ↦₆₄ w832) ∗
        ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ loBytes7 w864) ∗
        ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ loBytes7 w888) ∗
        v9_decCellsAt (fsp + 1888#64) bs ∗ ((fsp + 2272#64) ↦₆₄ w2272) ∗
        ((fsp + 2280#64) ↦₆₄ w2280) ∗ Rest ∗ A.pool lim st s)
      (fun s1 P1 =>
        (P1 ⊢ ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
          ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
          ((fsp + 104#64) ↦₆₄ v9_wordAt bs 376) ∗ ((fsp + 112#64) ↦₆₄ w2272) ∗
          ((fsp + 120#64) ↦₆₄ w2280) ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
          ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 160#64) ↦₆₄ v9_wordAt bs 312) ∗
          ((fsp + 172#64) ↦₃₂ (loByte (v9_wordAt bs 8)).zeroExtend 32) ∗
          ((fsp + 192#64) ↦₆₄ v9_wordAt bs 360) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 208#64) ↦₆₄ rkPtr) ∗
          ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ v9_wordAt bs 344) ∗
          ((fsp + 232#64) ↦₆₄ v9_wordAt bs 296) ∗
          ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte ep))) ∗
          ((fsp + 247#64) ↦₆₄ ep) ∗
          ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs 48) ∗
          ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs 80) ∗
          ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs 112) ∗
          ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs 144) ∗
          ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs 176) ∗
          ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs 208) ∗
          ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs 240) ∗
          ((fsp + 832#64) ↦₆₄ v9_wordAt bs 256) ∗
          ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)) ∗
          ((fsp + 864#64) ↦ₛ loBytes7 (v9_wordAt bs 24 >>> 8)) ∗
          ((fsp + 880#64) ↦₆₄ unshiftWord ct1Len (loByte ep)) ∗
          ((fsp + 888#64) ↦ₛ loBytes7 (ep >>> 8)) ∗
          v9_decCellsAt (fsp + 1888#64) bs ∗ ((fsp + 2272#64) ↦₆₄ w2272) ∗
          ((fsp + 2280#64) ↦₆₄ w2280) ∗ Rest ∗ A.pool lim st s1) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x0 = esPtr ∧ s1.readReg64 .x1 = v9_wordAt bs 336 ∧
        s1.readReg64 .x2 = v9_wordAt bs 264 ∧ s1.readReg32 .x3 = esLen.extractLsb' 0 32 ∧
        s1.readReg64 .x4 = ct1Cap ∧ s1.readReg64 .x5 = ct1Ptr ∧ s1.readReg64 .x6 = fsp + 576#64 ∧
        s1.readReg64 .x7 = v9_wordAt bs 0 ∧ s1.readReg64 .x8 = 11#64 ∧ s1.readReg64 .x9 = hdrCap ∧
        s1.readReg64 .x10 = v9_wordAt bs 304 ∧ s1.readReg64 .x11 = v9_wordAt bs 272 ∧
        s1.readReg64 .x12 = v9_wordAt bs 328 ∧ s1.readReg64 .x13 = mkCap ∧
        s1.readReg64 .x14 = hdrPtr ∧ s1.readReg64 .x15 = rkCap ∧
        s1.readReg64 .x16 = v9_wordAt bs 368 ∧ s1.readReg64 .x17 = esCap ∧
        s1.readReg64 .x18 = hdrLen ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x20 = rkLen ∧
        s1.readReg32 .x21 = (loByte ct1Len).zeroExtend 32 ∧
        s1.readReg64 .x22 = v9_wordAt bs 280 ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x24 = v9_wordAt bs 288 ∧ s1.readReg64 .x25 = mkPtr ∧
        s1.readReg64 .x26 = v9_wordAt bs 320 ∧ s1.readReg64 .x27 = esLen >>> 8 ∧
        s1.readReg32 .x27 = (esLen >>> 8).extractLsb' 0 32 ∧
        s1.readReg64 .x28 = v9_wordAt bs 352 ∧ s1.readReg64 .x30 = mkLen ∧
        TraceCalleeSaved s1 s0) := by
  have hwp := v9_step_3044_ok_to_8180_placed (ext := ext) s0 s fsp out
    rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep
    w104 w112 w120 w160 w192 w208 w224 w232 w832 w864 w880 w888 w2272 w2280 d172
    q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848 bs
    (Rest ∗ A.pool lim st s)
    hfsp_align hw0_lt hpc hrun hsp hx19 hx21 hx24 hx25 hx26 hx28 htr
  refine SepWP.mono hwp fun s1 P1 _ _ ⟨hP1, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP1
  exact ⟨Entails.trans hP1 (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-! ## 3. Shared `+7084` Error-Exit Sequencing Combiners -/

/-- Fixed-state (`0`-event) sequencer into `+7084 -> s0.x30` under `RustCliAllocBudget M`. -/
theorem v9_seq_err_7084_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64) (P : SepProp) (err : Error)
    {Q : State → Prop}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_eq : fsp = s0.sp - 2400#64)
    (hstep : SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s P
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          A.pool lim st sm ∗
          memRegion pbA optProtoInnerStateSize) ∧
        Q sm))
    (hQ : ∀ sm, Q sm →
      sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err ∧ TraceCalleeSaved sm s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
          memRegion pbA optProtoInnerStateSize ∗
          A.pool lim st sf ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine seq_clean_st (mid := lsmpl.base 333 + 7084#64)
    (P_mid := fun sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      A.pool lim st sm ∗
      memRegion pbA optProtoInnerStateSize)
    (Q := Q) hstep ?_
  intro sm hpcm hrunm hq
  obtain ⟨hspm, hx19m, herr_m, htrm⟩ := hQ sm hq
  rw [hfsp_eq] at hspm
  refine SepWP.mono (v9_states_from_pb_err_7084_placed_budget A lim st (F := F) s0 sm out err
    (memRegion pbA optProtoInnerStateSize)
    hsp0_align hpcm hrunm hspm hx19m herr_m htrm) ?_
  intro sf Pf _ _ ⟨hPf, _, hrest⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hrest⟩

/-- `FreeOnlyEvs`-threading sequencer into `+7084 -> s0.x30` under `RustCliAllocBudget M`. -/
theorem v9_seq_err_7084_evs_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64) (P : SepProp) (err : Error)
    {Q : State → Prop}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_eq : fsp = s0.sp - 2400#64)
    (hstep : SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s P
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion (s0.sp - 2400#64) 2304 ∗
            statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            memRegion pbA optProtoInnerStateSize) ∧
          Q sm))
    (hQ : ∀ sm, Q sm →
      sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err ∧ TraceCalleeSaved sm s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine seq_clean_evs (mid := lsmpl.base 333 + 7084#64)
    (P_evs := fun evs sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      memRegion pbA optProtoInnerStateSize)
    (Q := Q) hstep ?_
  intro evs sm hevs hpcm hrunm hq
  obtain ⟨hspm, hx19m, herr_m, htrm⟩ := hQ sm hq
  rw [hfsp_eq] at hspm
  refine SepWP.mono
    (v9_states_from_pb_err_7084_placed_budget A lim (M.stepEvents evs st) (F := F) s0 sm out err
      (memRegion pbA optProtoInnerStateSize)
      hsp0_align hpcm hrunm hspm hx19m herr_m htrm) ?_
  intro sf Pf _ _ ⟨hPf, _, hrest⟩
  exact ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlacedBudgetAux
