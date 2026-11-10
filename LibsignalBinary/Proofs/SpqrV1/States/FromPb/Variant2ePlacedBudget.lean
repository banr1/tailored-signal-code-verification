/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2ePlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2e
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 1 (`KeysSampled`) — Part E

Relocatable Block-`333` `<PolyEncoder>::from_pb` call (`+4096`), result branches, and `Ok`
epilogue composition (`+6568 -> +8180 -> ret`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2ePlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.RustHeap
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 lsmpl lsρ sepWP_seq_lscl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (PolyEncoder PolynomialError ProtoPolynomialEncoder)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize)
open CryptoVerification.SpqrV1.Poly
  (polyEncoderAt polyEncoderSize protoPolynomialEncoderAt protoPolynomialEncoderSize
   resultPolyEncoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (EncoderFromPbGhost encoderFromPbStack fromPbResult loByte loBytes7 unshiftWord)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved epilogueOutFull epilogueStackGaps epilogueStackSlots mem64_entails
   overlapWord7 resultChunkedStatesAt sp_sub_2400_align statesFromPbSavedCells
   statesFromPbStack v1_encCellsAt v1_epilogueOutFull_entails_keysSampled
   v1_epilogueStackGaps_pack v1_memRegion_240_1648_split v1_memRegion_72_104_split
   v1_midQ128 v1_quadAt v1_wordAt v1_zext32_setWidth8)
open CryptoVerification.SpqrV1.Unchunked (vecU8Payload)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv encoderFromPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (FromPbAllocHooksPlacedBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333

@[local simp]
private theorem stripS_readReg32 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (ProofLib.stripS keep s).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

/-! ## Budget-Threaded `<PolyEncoder>::from_pb` Call at `+4096` (`bl lsmpl.base 374`) -/

private theorem v1_step_4096_to_374_placed_raw [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out u8 u32 u72 : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 4096#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64) (hx1 : s.readReg64 .x1 = fsp + 896#64)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = u8) (hx22 : s.readReg64 .x22 = u72)
    (hx23 : s.readReg64 .x23 = fsp + 848#64) (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx28 : s.readReg64 .x28 = u32) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 374) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧ sm.sp = fsp ∧ sm.readReg64 .x30 = (blkPl_333).base + 4100#64 ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧ sm.readReg64 .x1 = fsp + 896#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = u8 ∧ sm.readReg64 .x22 = u72 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x28 = u32 ∧ TraceCalleeSaved sm s0) := by
  change s.pc = (blkPl_333).base + 4096#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    (lsmpl.base 374) s P _
  wp_steps
  wp_done

private theorem v1_step_4096_to_374_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out u8 u32 u72 : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 4096#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64) (hx1 : s.readReg64 .x1 = fsp + 896#64)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = u8) (hx22 : s.readReg64 .x22 = u72)
    (hx23 : s.readReg64 .x23 = fsp + 848#64) (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx28 : s.readReg64 .x28 = u32) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 374) s (P ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢ P ∗ A.pool lim st sm) ∧ VmPreserved s sm ∧ sm.sp = fsp ∧
        sm.readReg64 .x30 = (blkPl_333).base + 4100#64 ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧ sm.readReg64 .x1 = fsp + 896#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = u8 ∧ sm.readReg64 .x22 = u72 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x28 = u32 ∧ TraceCalleeSaved sm s0) := by
  have hwp : SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374) s (P ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢ P ∗ A.pool lim st s) ∧ VmPreserved s sm ∧ sm.sp = fsp ∧
        sm.readReg64 .x30 = (blkPl_333).base + 4100#64 ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧ sm.readReg64 .x1 = fsp + 896#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = u8 ∧ sm.readReg64 .x22 = u72 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x28 = u32 ∧ TraceCalleeSaved sm s0) :=
    sepWP_lsBlock_vmPreserved blkLib_eq_333
      isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
      (v1_step_4096_to_374_placed_raw (ext := vmTrapHooks) s0
        (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
        fsp out u8 u32 u72 (P ∗ A.pool lim st s)
        (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
        (by simpa using hx0) (by simpa using hx1) (by simpa using hx19)
        (by simpa using hx21) (by simpa using hx22) (by simpa using hx23)
        (by simpa using hx25) (by simpa using hx28)
        ⟨by simpa using htr.1, by simpa using htr.2⟩)
      fun sm Pm hvm
        ⟨hPm, hsp_m, hlr_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx23_m, hx25_m, hx28_m, htr_m⟩ =>
        ⟨hPm, hvm, by simpa using hsp_m, by simpa using hlr_m,
         by simpa using hx0_m, by simpa using hx1_m, by simpa using hx19_m,
         by simpa using hx21_m, by simpa using hx22_m, by simpa using hx23_m,
         by simpa using hx25_m, by simpa using hx28_m,
         ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- Standalone total-correctness (`SepWP`) call `<PolyEncoder>::from_pb` at `+4096 -> +4100`
    (`bl lsmpl.base 374`, Block `333` calling Block `374`) under `RustCliAllocBudget M`. -/
theorem v1_encoder_call_4096_to_4100_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (henc : Variant2aPlacedBudget.EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp out _pbA u8 u32 u72 : BitVec 64) (pbEnc : ProtoPolynomialEncoder) (Rest : SepProp)
    (hfits : FitsEnv M lim st (EncoderFromPbAllocEnv pbEnc))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_len : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hpc : s.pc = lsmpl.base 333 + 4096#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64) (hx1 : s.readReg64 .x1 = fsp + 896#64)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = u8) (hx22 : s.readReg64 .x22 = u72)
    (hx23 : s.readReg64 .x23 = fsp + 848#64) (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx28 : s.readReg64 .x28 = u32) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 4100#64) s
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc (fsp + 896#64) pbEnc ∗
        A.pool lim st s ∗ Rest)
      (fun s1 P1 =>
        ∃ evs : List AllocEvent,
          EncoderFromPbEnv pbEnc evs ∧
          (P1 ⊢
            stackAt fsp encoderFromPbStack ∗
            resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (fromPbResult pbEnc) ∗
            memRegion (fsp + 896#64) protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) s1 ∗ Rest) ∧
          s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x21 = u8 ∧
          s1.readReg64 .x22 = u72 ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
          s1.readReg64 .x25 = fsp + 1792#64 ∧ s1.readReg64 .x28 = u32 ∧
          TraceCalleeSaved s1 s0) := by
  have hsub := Variant2aPlacedBudget.v1_encoder_from_pb_ok_at_statesFromPb_placed henc
  have hstep := v1_step_4096_to_374_placed_budget (ext := ext) A lim st s0 s fsp out u8 u32 u72
    (stackAt fsp encoderFromPbStack ∗
      memRegion (fsp + 1888#64) polyEncoderSize ∗
      protoPolynomialEncoderAt A.repAlloc (fsp + 896#64) pbEnc ∗ Rest)
    hpc hrun hsp hx0 hx1 hx19 hx21 hx22 hx23 hx25 hx28 htr
  refine Variant2aPlacedBudget.seq_clean_lscl_st hcl
    (P_mid := fun sm =>
      (memRegion (fsp + 1888#64) polyEncoderSize ∗
       protoPolynomialEncoderAt A.repAlloc (fsp + 896#64) pbEnc ∗
       A.pool lim st sm ∗ stackAt fsp encoderFromPbStack) ∗ Rest)
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono hstep fun sm Pm _ _ ⟨hPm, hrest⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hrest⟩))
    ?_
  intro sm hpc_m hrun_m hcl_m
    ⟨_hvm_m, hsp_m, hlr_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx23_m, hx25_m, hx28_m, htr_m⟩
  have hsp_align_m : sm.spAligned = true := by
    unfold State.spAligned; rw [hsp_m]; exact hfsp_align
  have hpre_ent :
      memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc (fsp + 896#64) pbEnc ∗
        A.pool lim st sm ∗ stackAt fsp encoderFromPbStack ⊢
      (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)).pre
        (EncoderFromPbGhost.mk (fsp + 1888#64) (fsp + 896#64) pbEnc, st) sm := by
    dsimp only [withLsCodeLoaded, encoderFromPbSpec]
    rw [hsp_m, sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl sm.mem⌝, ← sepConj_assoc]
    exact Entails.pure_right hcl_m
      (Entails.pure_right ⟨hx0_m, hx1_m, hpts_len, hfits,
        by change LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (sm.readReg64 .x30); rw [show sm.readReg64 .x30 = _ from hlr_m]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 333 _ (by decide) (by decide)⟩ (Entails.refl _))
  refine SepWP.call_subroutine_frame hsub
    (x := (EncoderFromPbGhost.mk (fsp + 1888#64) (fsp + 896#64) pbEnc, st))
    (F := Rest)
    hpc_m hrun_m hsp_align_m hlr_m
    (fun R' hm => by
      rw [sepConj_assoc] at hm
      exact Satisfies.mono (sepConj_mono_left hpre_ent) hm)
    (fun _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    ?_
    (fun _ _ _ hm => False.elim (not_satisfies_false_sepConj hm))
  intro s1 hpc1 hrun1 hsp1 hcs1
  dsimp only [withLsCodeLoaded, encoderFromPbSpec]
  rw [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_elim; intro evs
  rw [sepConj_assoc]
  apply ProofLib.SepWP.pure_elim; rintro ⟨htr_s1, _hacp_s1, henv⟩
  apply ProofLib.SepWP.done hpc1 hrun1
  refine ⟨evs, henv, ?_,
    by rw [hsp1, hsp_m], by rw [hcs1.1, hx19_m], by rw [hcs1.2.2.1, hx21_m],
    by rw [hcs1.2.2.2.1, hx22_m], by rw [hcs1.2.2.2.2.1, hx23_m],
    by rw [hcs1.2.2.2.2.2.2.1, hx25_m], by rw [hcs1.2.2.2.2.2.2.2.2.2.1, hx28_m],
    ⟨htr_s1.trans htr_m.1, hcs1.2.2.2.2.2.2.2.2.2.2.2.trans htr_m.2⟩⟩
  rw [hsp_m]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Continuation-style total-correctness (`SepWP`) call `<PolyEncoder>::from_pb` at `+4096`,
    supplying `LibsignalCodeLoaded lsmpl s1.mem` and `EncoderFromPbEnv pbEnc evs` to `hnext`. -/
theorem v1_encoder_call_4096_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (henc : Variant2aPlacedBudget.EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (target_pc fsp out pbA u8 u32 u72 : BitVec 64)
    (pbEnc : ProtoPolynomialEncoder) (Rest : SepProp) (post : State → SepProp → Prop)
    (hfits : FitsEnv M lim st (EncoderFromPbAllocEnv pbEnc))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_len : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hpc : s.pc = lsmpl.base 333 + 4096#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64) (hx1 : s.readReg64 .x1 = fsp + 896#64)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = u8) (hx22 : s.readReg64 .x22 = u72)
    (hx23 : s.readReg64 .x23 = fsp + 848#64) (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx28 : s.readReg64 .x28 = u32) (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (evs : List AllocEvent),
      EncoderFromPbEnv pbEnc evs →
      ∀ (s1 : State),
        s1.pc = lsmpl.base 333 + 4100#64 → s1.status = .Running →
        LibsignalCodeLoaded lsmpl s1.mem →
        (s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x21 = u8 ∧
         s1.readReg64 .x22 = u72 ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
         s1.readReg64 .x25 = fsp + 1792#64 ∧ s1.readReg64 .x28 = u32 ∧
         TraceCalleeSaved s1 s0) →
        SepWP (lsProg_333 (Rust.withPanics ext)) target_pc s1
          (stackAt fsp encoderFromPbStack ∗
           resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (fromPbResult pbEnc) ∗
           memRegion (fsp + 896#64) protoPolynomialEncoderSize ∗
           A.pool lim (M.stepEvents evs st) s1 ∗ Rest)
          post) :
    SepWP (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc (fsp + 896#64) pbEnc ∗
        A.pool lim st s ∗ Rest)
      post := by
  have hcall := v1_encoder_call_4096_to_4100_placed_sepWP henc st s0 s hcl fsp out pbA u8 u32 u72
    pbEnc Rest hfits hfsp_align hpts_len hpc hrun hsp hx0 hx1 hx19 hx21 hx22 hx23 hx25 hx28 htr
  exact sepWP_seq_lscl hcl (SepWP.mono hcall fun s1 _P1 hpc1 hrun1 ⟨evs, henv, hP1, hregs⟩ hcl1 =>
    SepWP.weaken_pre hP1 (hnext evs henv s1 hpc1 hrun1 hcl1 hregs))

theorem v1_encoder_call_4096_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (henc : Variant2aPlacedBudget.EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (target_pc fsp out pbA u8 u32 u72 : BitVec 64)
    (pbEnc : ProtoPolynomialEncoder) (Rest : SepProp) (post : State → SepProp → Prop)
    (hfits : FitsEnv M lim st (EncoderFromPbAllocEnv pbEnc))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_len : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hpc : s.pc = lsmpl.base 333 + 4096#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64) (hx1 : s.readReg64 .x1 = fsp + 896#64)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = u8) (hx22 : s.readReg64 .x22 = u72)
    (hx23 : s.readReg64 .x23 = fsp + 848#64) (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx28 : s.readReg64 .x28 = u32) (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (evs : List AllocEvent),
      EncoderFromPbEnv pbEnc evs →
      ∀ (s1 : State),
        s1.pc = lsmpl.base 333 + 4100#64 → s1.status = .Running →
        LibsignalCodeLoaded lsmpl s1.mem →
        (s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x21 = u8 ∧
         s1.readReg64 .x22 = u72 ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
         s1.readReg64 .x25 = fsp + 1792#64 ∧ s1.readReg64 .x28 = u32 ∧
         TraceCalleeSaved s1 s0) →
        SepWP (lsProg_333 (Rust.withPanics ext)) target_pc s1
          (stackAt fsp encoderFromPbStack ∗
           resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (fromPbResult pbEnc) ∗
           memRegion (fsp + 896#64) protoPolynomialEncoderSize ∗
           A.pool lim (M.stepEvents evs st) s1 ∗ Rest)
          post) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗
        memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc (fsp + 896#64) pbEnc ∗
        A.pool lim st s ∗ Rest)
      post Qp :=
  SepWPp.of_sepWP_ret
    (v1_encoder_call_4096_placed_sepWP henc st s0 s hcl target_pc fsp out pbA u8 u32 u72
      pbEnc Rest post hfits hfsp_align hpts_len hpc hrun hsp hx0 hx1 hx19 hx21 hx22 hx23
      hx25 hx28 htr hnext)

/-! ## `VmPreserved` & Pool-Threaded Result Branch Steps (`+4100 -> +4116 | +6568`) -/

/-- `VmPreserved`-strengthened placed `<PolyEncoder>::from_pb` `Err` branch (`+4100 -> +4116`). -/
theorem v1_encoder_err_4100_4116_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out u8 u32 u72 : BitVec 64)
    (err : PolynomialError) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4100#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = u8) (hx22 : s.readReg64 .x22 = u72)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 4116#64) s
      (resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ memRegion (fsp + 1888#64) 400 ∗ Rest) ∧ VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x22 = u72 ∧
        s1.readReg64 .x25 = fsp + 1792#64 ∧ s1.readReg64 .x26 = u8 ∧
        s1.readReg64 .x28 = u32 ∧ TraceCalleeSaved s1 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2ePlaced.v1_encoder_err_4100_4116_placed
      (A := A) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out u8 u32 u72 err Rest hfsp_align
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx21) (by simpa using hx22)
      (by simpa using hx25) (by simpa using hx28)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s1 P1 hvm ⟨hP1, hsp1, hx19_1, hx22_1, hx25_1, hx26_1, hx28_1, htr1⟩ =>
      ⟨hP1, hvm, by simpa using hsp1, by simpa using hx19_1, by simpa using hx22_1,
       by simpa using hx25_1, by simpa using hx26_1, by simpa using hx28_1,
       ⟨by simpa using htr1.1, by simpa using htr1.2⟩⟩

theorem v1_encoder_err_4100_4116_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out u8 u32 u72 : BitVec 64)
    (err : PolynomialError) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4100#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = u8) (hx22 : s.readReg64 .x22 = u72)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 4116#64) s
      (resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err) ∗
        Rest ∗ A.pool lim st s)
      (fun s1 P1 =>
        (P1 ⊢ memRegion (fsp + 1888#64) 400 ∗ Rest ∗ A.pool lim st s1) ∧ VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x22 = u72 ∧
        s1.readReg64 .x25 = fsp + 1792#64 ∧ s1.readReg64 .x26 = u8 ∧
        s1.readReg64 .x28 = u32 ∧ TraceCalleeSaved s1 s0) := by
  have hwp := v1_encoder_err_4100_4116_placed (A := A.repAlloc) (ext := ext)
    s0 s fsp out u8 u32 u72 err (Rest ∗ A.pool lim st s)
    hfsp_align hpc hrun hsp hx19 hx21 hx22 hx25 hx28 htr
  refine SepWP.mono hwp fun s1 P1 _ _ ⟨hP1, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP1
  exact ⟨hP1, hvm, hrest⟩

/-- `VmPreserved`-strengthened placed `<PolyEncoder>::from_pb` `Ok` branch (`+4100 -> +6568`). -/
theorem v1_encoder_ok_4100_6568_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out tag u8 u32 u72 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (htag : tag = 0#64 ∨ tag = 1#64)
    (hpc : s.pc = lsmpl.base 333 + 4100#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = u8) (hx22 : s.readReg64 .x22 = u72)
    (hx23 : s.readReg64 .x23 = fsp + 848#64) (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx28 : s.readReg64 .x28 = u32) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6568#64) s
      (((fsp + 1888#64) ↦₆₄ tag) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ ((fsp + 1888#64) ↦₆₄ tag) ∗ Rest) ∧ VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x15 = tag ∧ s1.readReg64 .x19 = out ∧
        s1.readReg64 .x21 = u8 ∧ s1.readReg64 .x22 = u72 ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧ s1.readReg64 .x25 = fsp + 1792#64 ∧
        s1.readReg64 .x26 = u8 ∧ s1.readReg64 .x28 = u32 ∧ TraceCalleeSaved s1 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2ePlaced.v1_encoder_ok_4100_6568_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out tag u8 u32 u72 Rest hfsp_align htag
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx21) (by simpa using hx22)
      (by simpa using hx23) (by simpa using hx25) (by simpa using hx28)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s1 P1 hvm
      ⟨hP1, hsp1, hx15_1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hx28_1, htr1⟩ =>
      ⟨hP1, hvm, by simpa using hsp1, by simpa using hx15_1, by simpa using hx19_1,
       by simpa using hx21_1, by simpa using hx22_1, by simpa using hx23_1,
       by simpa using hx25_1, by simpa using hx26_1, by simpa using hx28_1,
       ⟨by simpa using htr1.1, by simpa using htr1.2⟩⟩

theorem v1_encoder_ok_4100_6568_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out tag u8 u32 u72 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (htag : tag = 0#64 ∨ tag = 1#64)
    (hpc : s.pc = lsmpl.base 333 + 4100#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = u8) (hx22 : s.readReg64 .x22 = u72)
    (hx23 : s.readReg64 .x23 = fsp + 848#64) (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx28 : s.readReg64 .x28 = u32) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6568#64) s
      (((fsp + 1888#64) ↦₆₄ tag) ∗ Rest ∗ A.pool lim st s)
      (fun s1 P1 =>
        (P1 ⊢ ((fsp + 1888#64) ↦₆₄ tag) ∗ Rest ∗ A.pool lim st s1) ∧ VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x15 = tag ∧ s1.readReg64 .x19 = out ∧
        s1.readReg64 .x21 = u8 ∧ s1.readReg64 .x22 = u72 ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧ s1.readReg64 .x25 = fsp + 1792#64 ∧
        s1.readReg64 .x26 = u8 ∧ s1.readReg64 .x28 = u32 ∧ TraceCalleeSaved s1 s0) := by
  have hwp := v1_encoder_ok_4100_6568_placed (ext := ext)
    s0 s fsp out tag u8 u32 u72 (Rest ∗ A.pool lim st s)
    hfsp_align htag hpc hrun hsp hx19 hx21 hx22 hx23 hx25 hx28 htr
  refine SepWP.mono hwp fun s1 P1 _ _ ⟨hP1, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP1
  exact ⟨hP1, hvm, hrest⟩

/-! ## `VmPreserved` & Pool-Threaded `KeysSampled` Staging & Completion (`+6568 -> +8180 -> ret`) -/

/-- `VmPreserved`-strengthened placed Variant-1 staging step (`+6568 -> +8180`, Block `333`). -/
theorem v1_keysSampled_6568_8180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out tag pa1 pa2 u8 u16 u32 u40 u72 u96 u104 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) (hi32 idx : BitVec 32)
    (w160 w208 w224 w832 w864 w880 w888 : BitVec 64) (d172 : BitVec 32)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848 : BitVec 128)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 6568#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx15 : s.readReg64 .x15 = tag) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx26 : s.readReg64 .x26 = u8)
    (hx28 : s.readReg64 .x28 = u32) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 8180#64) s
      (((fsp + 64#64) ↦₆₄ u104) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗ ((fsp + 172#64) ↦₃₂ d172) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ pa1) ∗
        ((fsp + 208#64) ↦₆₄ w208) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
        ((fsp + 232#64) ↦₆₄ u96) ∗
        ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗
        ((fsp + 640#64) ↦₁₂₈ q640) ∗ ((fsp + 656#64) ↦₁₂₈ q656) ∗
        ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
        ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗
        ((fsp + 736#64) ↦₁₂₈ q736) ∗ ((fsp + 752#64) ↦₁₂₈ q752) ∗
        ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
        ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗
        ((fsp + 832#64) ↦₆₄ w832) ∗
        ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ loBytes7 w864) ∗
        ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ loBytes7 w888) ∗
        ((fsp + 1888#64) ↦₆₄ tag) ∗ v1_encCellsAt (fsp + 1888#64) bs ∗
        ((fsp + 2280#64) ↦₆₄ (hi32 ++ idx)) ∗ memRegion (fsp + 2288#64) 16 ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 64#64) ↦₆₄ u104) ∗ ((fsp + 160#64) ↦₆₄ u96) ∗
          ((fsp + 172#64) ↦₃₂ (loByte (v1_wordAt bs 128)).zeroExtend 32) ∗
          ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ pa1) ∗
          ((fsp + 208#64) ↦₆₄ v1_wordAt bs 0) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
          ((fsp + 224#64) ↦₆₄ u32) ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
          ((fsp + 608#64) ↦₁₂₈ v1_quadAt bs 152) ∗ ((fsp + 624#64) ↦₁₂₈ v1_quadAt bs 168) ∗
          ((fsp + 640#64) ↦₁₂₈ v1_quadAt bs 184) ∗ ((fsp + 656#64) ↦₁₂₈ v1_quadAt bs 200) ∗
          ((fsp + 672#64) ↦₁₂₈ v1_quadAt bs 216) ∗ ((fsp + 688#64) ↦₁₂₈ v1_quadAt bs 232) ∗
          ((fsp + 704#64) ↦₁₂₈ v1_quadAt bs 248) ∗ ((fsp + 720#64) ↦₁₂₈ v1_quadAt bs 264) ∗
          ((fsp + 736#64) ↦₁₂₈ v1_quadAt bs 280) ∗ ((fsp + 752#64) ↦₁₂₈ v1_quadAt bs 296) ∗
          ((fsp + 768#64) ↦₁₂₈ v1_quadAt bs 312) ∗ ((fsp + 784#64) ↦₁₂₈ v1_quadAt bs 328) ∗
          ((fsp + 800#64) ↦₁₂₈ v1_quadAt bs 344) ∗ ((fsp + 816#64) ↦₁₂₈ v1_quadAt bs 360) ∗
          ((fsp + 832#64) ↦₆₄ v1_wordAt bs 376) ∗
          ((fsp + 848#64) ↦₁₂₈ v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)) ∗
          ((fsp + 864#64) ↦ₛ loBytes7 (v1_wordAt bs 144 >>> 8)) ∗
          ((fsp + 880#64) ↦₆₄ unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) ∗
          ((fsp + 888#64) ↦ₛ loBytes7 (v1_wordAt bs 112 >>> 8)) ∗
          ((fsp + 1888#64) ↦₁₂₈ (v1_wordAt bs 0 ++ tag)) ∗
          ((fsp + 1904#64) ↦₁₂₈ (v1_wordAt bs 16 ++ v1_wordAt bs 8)) ∗
          ((fsp + 1920#64) ↦₆₄ v1_wordAt bs 24) ∗ memRegion (fsp + 1928#64) 376 ∗ Rest) ∧
        VmPreserved s s1 ∧ s1.sp = fsp ∧ s1.readReg64 .x6 = fsp + 576#64 ∧
        s1.readReg64 .x19 = out ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x8 = 3#64 ∧ s1.readReg64 .x15 = tag ∧
        s1.readReg64 .x20 = v1_wordAt bs 8 ∧ s1.readReg64 .x13 = v1_wordAt bs 16 ∧
        s1.readReg64 .x25 = v1_wordAt bs 24 ∧ s1.readReg64 .x30 = v1_wordAt bs 32 ∧
        s1.readReg64 .x9 = v1_wordAt bs 40 ∧ s1.readReg64 .x14 = v1_wordAt bs 48 ∧
        s1.readReg64 .x18 = v1_wordAt bs 56 ∧ s1.readReg64 .x17 = v1_wordAt bs 64 ∧
        s1.readReg64 .x0 = v1_wordAt bs 72 ∧
        s1.readReg32 .x3 = ((v1_wordAt bs 80).extractLsb' 0 8).zeroExtend 32 ∧
        s1.readReg32 .x27 = (v1_wordAt bs 80).extractLsb' 8 32 ∧
        ((s1.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = (v1_wordAt bs 80).extractLsb' 40 16 ∧
        ((s1.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = (v1_wordAt bs 80).extractLsb' 56 8 ∧
        s1.readReg64 .x4 = v1_wordAt bs 88 ∧ s1.readReg64 .x5 = v1_wordAt bs 96 ∧
        s1.readReg32 .x21 = (loByte (v1_wordAt bs 104)).zeroExtend 32 ∧
        s1.readReg64 .x7 = v1_wordAt bs 120 ∧ s1.readReg64 .x2 = hi32 ++ idx ∧
        s1.readReg64 .x11 = u72 ∧ s1.readReg64 .x22 = pa1 ∧ s1.readReg64 .x24 = u72 ∧
        s1.readReg64 .x10 = pa2 ∧ s1.readReg64 .x26 = u8 ∧ s1.readReg64 .x12 = u16 ∧
        s1.readReg64 .x1 = 1152#64 ∧ s1.readReg64 .x28 = u40 ∧ s1.readReg64 .x16 = u104 ∧
        TraceCalleeSaved s1 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2ePlaced.v1_keysSampled_6568_8180_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out tag pa1 pa2 u8 u16 u32 u40 u72 u96 u104 bs hbs hi32 idx
      w160 w208 w224 w832 w864 w880 w888 d172
      q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848
      Rest hfsp_align
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx15) (by simpa using hx19) (by simpa using hx21)
      (by simpa using hx22) (by simpa using hx23) (by simpa using hx25)
      (by simpa using hx26) (by simpa using hx28)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s1 P1 hvm
      ⟨hP1, hsp1, hx6_1, hx19_1, hx23_1, hx8_1, hx15_1, hx20_1, hx13_1, hx25_1, hx30_1,
       hx9_1, hx14_1, hx18_1, hx17_1, hx0_1, hx3_1, hx27_1, hx27_hi16, hx27_hi8, hx4_1,
       hx5_1, hx21_1, hx7_1, hx2_1, hx11_1, hx22_1, hx24_1, hx10_1, hx26_1, hx12_1,
       hx1_1, hx28_1, hx16_1, htr1⟩ => by
      exact ⟨hP1, hvm, by simpa using hsp1, by simpa using hx6_1, by simpa using hx19_1,
        by simpa using hx23_1, by simpa using hx8_1, by simpa using hx15_1,
        by simpa using hx20_1, by simpa using hx13_1, by simpa using hx25_1,
        by simpa using hx30_1, by simpa using hx9_1, by simpa using hx14_1,
        by simpa using hx18_1, by simpa using hx17_1, by simpa using hx0_1,
        by simpa using hx3_1, by simpa using hx27_1, by simpa using hx27_hi16,
        by simpa using hx27_hi8, by simpa using hx4_1, by simpa using hx5_1,
        by simpa using hx21_1, by simpa using hx7_1, by simpa using hx2_1,
        by simpa using hx11_1, by simpa using hx22_1, by simpa using hx24_1,
        by simpa using hx10_1, by simpa using hx26_1, by simpa using hx12_1,
        by simpa using hx1_1, by simpa using hx28_1, by simpa using hx16_1,
        ⟨by simpa using htr1.1, by simpa using htr1.2⟩⟩

theorem v1_keysSampled_6568_8180_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out tag pa1 pa2 u8 u16 u32 u40 u72 u96 u104 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) (hi32 idx : BitVec 32)
    (w160 w208 w224 w832 w864 w880 w888 : BitVec 64) (d172 : BitVec 32)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848 : BitVec 128)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 6568#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx15 : s.readReg64 .x15 = tag) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx26 : s.readReg64 .x26 = u8)
    (hx28 : s.readReg64 .x28 = u32) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 8180#64) s
      (((fsp + 64#64) ↦₆₄ u104) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗ ((fsp + 172#64) ↦₃₂ d172) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ pa1) ∗
        ((fsp + 208#64) ↦₆₄ w208) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
        ((fsp + 232#64) ↦₆₄ u96) ∗
        ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗
        ((fsp + 640#64) ↦₁₂₈ q640) ∗ ((fsp + 656#64) ↦₁₂₈ q656) ∗
        ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
        ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗
        ((fsp + 736#64) ↦₁₂₈ q736) ∗ ((fsp + 752#64) ↦₁₂₈ q752) ∗
        ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
        ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗
        ((fsp + 832#64) ↦₆₄ w832) ∗
        ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ loBytes7 w864) ∗
        ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ loBytes7 w888) ∗
        ((fsp + 1888#64) ↦₆₄ tag) ∗ v1_encCellsAt (fsp + 1888#64) bs ∗
        ((fsp + 2280#64) ↦₆₄ (hi32 ++ idx)) ∗ memRegion (fsp + 2288#64) 16 ∗
        Rest ∗ A.pool lim st s)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 64#64) ↦₆₄ u104) ∗ ((fsp + 160#64) ↦₆₄ u96) ∗
          ((fsp + 172#64) ↦₃₂ (loByte (v1_wordAt bs 128)).zeroExtend 32) ∗
          ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ pa1) ∗
          ((fsp + 208#64) ↦₆₄ v1_wordAt bs 0) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
          ((fsp + 224#64) ↦₆₄ u32) ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
          ((fsp + 608#64) ↦₁₂₈ v1_quadAt bs 152) ∗ ((fsp + 624#64) ↦₁₂₈ v1_quadAt bs 168) ∗
          ((fsp + 640#64) ↦₁₂₈ v1_quadAt bs 184) ∗ ((fsp + 656#64) ↦₁₂₈ v1_quadAt bs 200) ∗
          ((fsp + 672#64) ↦₁₂₈ v1_quadAt bs 216) ∗ ((fsp + 688#64) ↦₁₂₈ v1_quadAt bs 232) ∗
          ((fsp + 704#64) ↦₁₂₈ v1_quadAt bs 248) ∗ ((fsp + 720#64) ↦₁₂₈ v1_quadAt bs 264) ∗
          ((fsp + 736#64) ↦₁₂₈ v1_quadAt bs 280) ∗ ((fsp + 752#64) ↦₁₂₈ v1_quadAt bs 296) ∗
          ((fsp + 768#64) ↦₁₂₈ v1_quadAt bs 312) ∗ ((fsp + 784#64) ↦₁₂₈ v1_quadAt bs 328) ∗
          ((fsp + 800#64) ↦₁₂₈ v1_quadAt bs 344) ∗ ((fsp + 816#64) ↦₁₂₈ v1_quadAt bs 360) ∗
          ((fsp + 832#64) ↦₆₄ v1_wordAt bs 376) ∗
          ((fsp + 848#64) ↦₁₂₈ v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)) ∗
          ((fsp + 864#64) ↦ₛ loBytes7 (v1_wordAt bs 144 >>> 8)) ∗
          ((fsp + 880#64) ↦₆₄ unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) ∗
          ((fsp + 888#64) ↦ₛ loBytes7 (v1_wordAt bs 112 >>> 8)) ∗
          ((fsp + 1888#64) ↦₁₂₈ (v1_wordAt bs 0 ++ tag)) ∗
          ((fsp + 1904#64) ↦₁₂₈ (v1_wordAt bs 16 ++ v1_wordAt bs 8)) ∗
          ((fsp + 1920#64) ↦₆₄ v1_wordAt bs 24) ∗ memRegion (fsp + 1928#64) 376 ∗
          Rest ∗ A.pool lim st s1) ∧
        VmPreserved s s1 ∧ s1.sp = fsp ∧ s1.readReg64 .x6 = fsp + 576#64 ∧
        s1.readReg64 .x19 = out ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x8 = 3#64 ∧ s1.readReg64 .x15 = tag ∧
        s1.readReg64 .x20 = v1_wordAt bs 8 ∧ s1.readReg64 .x13 = v1_wordAt bs 16 ∧
        s1.readReg64 .x25 = v1_wordAt bs 24 ∧ s1.readReg64 .x30 = v1_wordAt bs 32 ∧
        s1.readReg64 .x9 = v1_wordAt bs 40 ∧ s1.readReg64 .x14 = v1_wordAt bs 48 ∧
        s1.readReg64 .x18 = v1_wordAt bs 56 ∧ s1.readReg64 .x17 = v1_wordAt bs 64 ∧
        s1.readReg64 .x0 = v1_wordAt bs 72 ∧
        s1.readReg32 .x3 = ((v1_wordAt bs 80).extractLsb' 0 8).zeroExtend 32 ∧
        s1.readReg32 .x27 = (v1_wordAt bs 80).extractLsb' 8 32 ∧
        ((s1.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = (v1_wordAt bs 80).extractLsb' 40 16 ∧
        ((s1.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = (v1_wordAt bs 80).extractLsb' 56 8 ∧
        s1.readReg64 .x4 = v1_wordAt bs 88 ∧ s1.readReg64 .x5 = v1_wordAt bs 96 ∧
        s1.readReg32 .x21 = (loByte (v1_wordAt bs 104)).zeroExtend 32 ∧
        s1.readReg64 .x7 = v1_wordAt bs 120 ∧ s1.readReg64 .x2 = hi32 ++ idx ∧
        s1.readReg64 .x11 = u72 ∧ s1.readReg64 .x22 = pa1 ∧ s1.readReg64 .x24 = u72 ∧
        s1.readReg64 .x10 = pa2 ∧ s1.readReg64 .x26 = u8 ∧ s1.readReg64 .x12 = u16 ∧
        s1.readReg64 .x1 = 1152#64 ∧ s1.readReg64 .x28 = u40 ∧ s1.readReg64 .x16 = u104 ∧
        TraceCalleeSaved s1 s0) := by
  have hwp := v1_keysSampled_6568_8180_placed (ext := ext)
    s0 s fsp out tag pa1 pa2 u8 u16 u32 u40 u72 u96 u104 bs hbs hi32 idx
    w160 w208 w224 w832 w864 w880 w888 d172
    q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848
    (Rest ∗ A.pool lim st s)
    hfsp_align hpc hrun hsp hx15 hx19 hx21 hx22 hx23 hx25 hx26 hx28 htr
  refine SepWP.mono hwp fun s1 P1 _ _ ⟨hP1, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP1
  exact ⟨hP1, hvm, hrest⟩

set_option maxHeartbeats 800000 in
/-- Compose `+6568 -> +8180` with `Variant1bPlacedBudgetAux.states_from_pb_epilogue_8180_placed`
    and `v1_epilogueOutFull_entails_keysSampled`, parameterized by `allocMemcpyVmSpec`. -/
theorem v1_keysSampled_6568_ret_placed_of_memcpy [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ "memcpy") allocMemcpyVmSpec)
    (s0 s : State) (out tag pa1 pa2 u8 u16 u24 u32 u40 u48 u72 u96 u104 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hi32 : BitVec 32) (enc : PolyEncoder) (P_heap : SepProp)
    (hreloc :
      ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗
        (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
        polyEncoderAt A.repAlloc (out + 8#64) enc)
    (ek dk rootKey macKey : List (BitVec 8))
    (hek : u24 = BitVec.ofNat 64 ek.length) (hdk : u48 = BitVec.ofNat 64 dk.length)
    (hl1 : u72 = BitVec.ofNat 64 rootKey.length) (hl2 : u96 = BitVec.ofNat 64 macKey.length)
    (hu24_1152 : u24 = 1152#64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 6568#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx15 : s.readReg64 .x15 = tag) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = u8) (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
        memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗ memRegion (s0.sp - 2400#64 + 240#64) 1648 ∗
        ((s0.sp - 2400#64 + 1888#64) ↦₆₄ tag) ∗ v1_encCellsAt (s0.sp - 2400#64 + 1888#64) bs ∗
        ((s0.sp - 2400#64 + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ P_heap ∗
        vecU8Payload A.repAlloc u8 u16 ek ∗ vecU8Payload A.repAlloc u32 u40 dk ∗
        vecU8Payload A.repAlloc u72 pa1 rootKey ∗ vecU8Payload A.repAlloc u96 pa2 macKey ∗
        A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out
            (.ok (.keysSampled
              { uc := { ek := ek, dk := dk, auth := { rootKey := rootKey, macKey := macKey },
                        epoch := u104 },
                sending_hdr := enc })) ∗
          A.pool lim st sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s sf ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (v1_memRegion_72_104_split (s0.sp - 2400#64))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (mem64_entails (s0.sp - 2400#64 + 208#64))
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (v1_memRegion_240_1648_split (s0.sp - 2400#64))))))))))))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun w888 => ProofLib.SepWP.exists_left fun w880 =>
    ProofLib.SepWP.exists_left fun w864 => ProofLib.SepWP.exists_left fun q848 =>
    ProofLib.SepWP.exists_left fun w832 => ProofLib.SepWP.exists_left fun q816 =>
    ProofLib.SepWP.exists_left fun q800 => ProofLib.SepWP.exists_left fun q784 =>
    ProofLib.SepWP.exists_left fun q768 => ProofLib.SepWP.exists_left fun q752 =>
    ProofLib.SepWP.exists_left fun q736 => ProofLib.SepWP.exists_left fun q720 =>
    ProofLib.SepWP.exists_left fun q704 => ProofLib.SepWP.exists_left fun q688 =>
    ProofLib.SepWP.exists_left fun q672 => ProofLib.SepWP.exists_left fun q656 =>
    ProofLib.SepWP.exists_left fun q640 => ProofLib.SepWP.exists_left fun q624 =>
    ProofLib.SepWP.exists_left fun q608 => ProofLib.SepWP.exists_left fun w592 =>
    ProofLib.SepWP.exists_left fun q576 => ProofLib.SepWP.exists_left fun bs240 =>
    ProofLib.SepWP.exists_left fun w208 => ProofLib.SepWP.exists_left fun d172 =>
    ProofLib.SepWP.exists_left fun w160 => ProofLib.SepWP.exists_left fun w120 =>
    ProofLib.SepWP.exists_left fun w112 => ProofLib.SepWP.exists_left fun w104 =>
    ProofLib.SepWP.exists_left fun d92 => ?_
  have h6568 := v1_keysSampled_6568_8180_placed_budget (ext := ext) A lim st s0 s
    (s0.sp - 2400#64) out tag pa1 pa2 u8 u16 u32 u40 u72 u96 u104
    bs hbs hi32 enc.idx w160 w208 u32 w832 w864 w880 w888 d172
    q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
      ((s0.sp - 2400#64 + 92#64) ↦₃₂ d92) ∗ ((s0.sp - 2400#64 + 104#64) ↦₆₄ w104) ∗
      ((s0.sp - 2400#64 + 112#64) ↦₆₄ w112) ∗ ((s0.sp - 2400#64 + 120#64) ↦₆₄ w120) ∗
      ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 240#64) ↦ₛ bs240.val) ∗
      ((s0.sp - 2400#64 + 576#64) ↦₁₂₈ q576) ∗ ((s0.sp - 2400#64 + 592#64) ↦ₛ loBytes7 w592) ∗
      memRegion (s0.sp - 2400#64) 64 ∗ memRegion (s0.sp - 2400#64 + 72#64) 20 ∗
      memRegion (s0.sp - 2400#64 + 96#64) 8 ∗ memRegion (s0.sp - 2400#64 + 128#64) 32 ∗
      memRegion (s0.sp - 2400#64 + 168#64) 4 ∗ memRegion (s0.sp - 2400#64 + 568#64) 8 ∗
      memRegion (s0.sp - 2400#64 + 599#64) 9 ∗ memRegion (s0.sp - 2400#64 + 840#64) 8 ∗
      memRegion (s0.sp - 2400#64 + 871#64) 9 ∗ memRegion (s0.sp - 2400#64 + 895#64) 993 ∗
      statesFromPbSavedCells s0 ∗ P_heap ∗
      vecU8Payload A.repAlloc u8 u16 ek ∗ vecU8Payload A.repAlloc u32 u40 dk ∗
      vecU8Payload A.repAlloc u72 pa1 rootKey ∗ vecU8Payload A.repAlloc u96 pa2 macKey ∗ Rest)
    hfsp_align hpc hrun hsp hx15 hx19 hx21 hx22 hx23 hx25 hx26 hx28 htr
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) h6568) ?_
  intro s1 P1 hpc1 hrun1 ⟨hP1, hvm1, hsp1, hx6_1, hx19_1, hx23_1, hx8_1, hx15_1, hx20_1, hx13_1,
    hx25_1, hx30_1, hx9_1, hx14_1, hx18_1, hx17_1, hx0_1, hx3_1, hx27_1, hx27_hi16, hx27_hi8,
    hx4_1, hx5_1, hx21_1, hx7_1, hx2_1, hx11_1, hx22_1, hx24_1, hx10_1, hx26_1, hx12_1,
    hx1_1, hx28_1, hx16_1, htr1⟩
  have hgaps := v1_epilogueStackGaps_pack (s0.sp - 2400#64) u104 u16 pa2 pa1 u40
  have hP1' : P1 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
      epilogueStackSlots (s0.sp - 2400#64)
        d92 ((loByte (v1_wordAt bs 128)).zeroExtend 32)
        w104 w112 w120 u96 u48 (v1_wordAt bs 0) u32 u96 bs240.val q576 w592
        (v1_quadAt bs 152) (v1_quadAt bs 168) (v1_quadAt bs 184) (v1_quadAt bs 200)
        (v1_quadAt bs 216) (v1_quadAt bs 232) (v1_quadAt bs 248) (v1_quadAt bs 264)
        (v1_quadAt bs 280) (v1_quadAt bs 296) (v1_quadAt bs 312) (v1_quadAt bs 328)
        (v1_quadAt bs 344) (v1_quadAt bs 360) (v1_wordAt bs 376)
        (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144))
        (v1_wordAt bs 144 >>> 8)
        (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112)))
        (v1_wordAt bs 112 >>> 8)
        (v1_wordAt bs 0 ++ tag) (v1_wordAt bs 16 ++ v1_wordAt bs 8) (v1_wordAt bs 24) ∗
      epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗
      (P_heap ∗ vecU8Payload A.repAlloc u8 u16 ek ∗ vecU8Payload A.repAlloc u32 u40 dk ∗
       vecU8Payload A.repAlloc u72 pa1 rootKey ∗ vecU8Payload A.repAlloc u96 pa2 macKey ∗ Rest) ∗
      A.pool lim st s1 := by
    refine Entails.trans hP1 ?_
    unfold epilogueStackSlots
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
       memRegion (s0.sp - 2400#64 + 72#64) 20 ∗ memRegion (s0.sp - 2400#64 + 96#64) 8 ∗
       memRegion (s0.sp - 2400#64 + 128#64) 32 ∗ memRegion (s0.sp - 2400#64 + 168#64) 4 ∗
       ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
       ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
       memRegion (s0.sp - 2400#64 + 568#64) 8 ∗ memRegion (s0.sp - 2400#64 + 599#64) 9 ∗
       memRegion (s0.sp - 2400#64 + 840#64) 8 ∗ memRegion (s0.sp - 2400#64 + 871#64) 9 ∗
       memRegion (s0.sp - 2400#64 + 895#64) 993 ∗ memRegion (s0.sp - 2400#64 + 1928#64) 376) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       (((s0.sp - 2400#64 + 92#64) ↦₃₂ d92) ∗ ((s0.sp - 2400#64 + 104#64) ↦₆₄ w104) ∗
        ((s0.sp - 2400#64 + 112#64) ↦₆₄ w112) ∗ ((s0.sp - 2400#64 + 120#64) ↦₆₄ w120) ∗
        ((s0.sp - 2400#64 + 160#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 172#64) ↦₃₂ (loByte (v1_wordAt bs 128)).zeroExtend 32) ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 208#64) ↦₆₄ v1_wordAt bs 0) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        ((s0.sp - 2400#64 + 240#64) ↦ₛ bs240.val) ∗ ((s0.sp - 2400#64 + 576#64) ↦₁₂₈ q576) ∗
        ((s0.sp - 2400#64 + 592#64) ↦ₛ loBytes7 w592) ∗
        ((s0.sp - 2400#64 + 608#64) ↦₁₂₈ v1_quadAt bs 152) ∗
        ((s0.sp - 2400#64 + 624#64) ↦₁₂₈ v1_quadAt bs 168) ∗
        ((s0.sp - 2400#64 + 640#64) ↦₁₂₈ v1_quadAt bs 184) ∗
        ((s0.sp - 2400#64 + 656#64) ↦₁₂₈ v1_quadAt bs 200) ∗
        ((s0.sp - 2400#64 + 672#64) ↦₁₂₈ v1_quadAt bs 216) ∗
        ((s0.sp - 2400#64 + 688#64) ↦₁₂₈ v1_quadAt bs 232) ∗
        ((s0.sp - 2400#64 + 704#64) ↦₁₂₈ v1_quadAt bs 248) ∗
        ((s0.sp - 2400#64 + 720#64) ↦₁₂₈ v1_quadAt bs 264) ∗
        ((s0.sp - 2400#64 + 736#64) ↦₁₂₈ v1_quadAt bs 280) ∗
        ((s0.sp - 2400#64 + 752#64) ↦₁₂₈ v1_quadAt bs 296) ∗
        ((s0.sp - 2400#64 + 768#64) ↦₁₂₈ v1_quadAt bs 312) ∗
        ((s0.sp - 2400#64 + 784#64) ↦₁₂₈ v1_quadAt bs 328) ∗
        ((s0.sp - 2400#64 + 800#64) ↦₁₂₈ v1_quadAt bs 344) ∗
        ((s0.sp - 2400#64 + 816#64) ↦₁₂₈ v1_quadAt bs 360) ∗
        ((s0.sp - 2400#64 + 832#64) ↦₆₄ v1_wordAt bs 376) ∗
        ((s0.sp - 2400#64 + 848#64) ↦₁₂₈ v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)) ∗
        ((s0.sp - 2400#64 + 864#64) ↦ₛ loBytes7 (v1_wordAt bs 144 >>> 8)) ∗
        ((s0.sp - 2400#64 + 880#64) ↦₆₄ unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) ∗
        ((s0.sp - 2400#64 + 888#64) ↦ₛ loBytes7 (v1_wordAt bs 112 >>> 8)) ∗
        ((s0.sp - 2400#64 + 1888#64) ↦₁₂₈ (v1_wordAt bs 0 ++ tag)) ∗
        ((s0.sp - 2400#64 + 1904#64) ↦₁₂₈ (v1_wordAt bs 16 ++ v1_wordAt bs 8)) ∗
        ((s0.sp - 2400#64 + 1920#64) ↦₆₄ v1_wordAt bs 24)) ∗
       statesFromPbSavedCells s0 ∗
       (P_heap ∗ vecU8Payload A.repAlloc u8 u16 ek ∗ vecU8Payload A.repAlloc u32 u40 dk ∗
        vecU8Payload A.repAlloc u72 pa1 rootKey ∗ vecU8Payload A.repAlloc u96 pa2 macKey ∗ Rest) ∗
       A.pool lim st s1) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hgaps) (Entails.of_eq (by sep_ac_rfl))
  have hep := Variant1bPlacedBudgetAux.states_from_pb_epilogue_8180_placed A lim st hmemcpy_ok s0 s1 out
    d92 ((loByte (v1_wordAt bs 128)).zeroExtend 32)
    w104 w112 w120 u96 u48 (v1_wordAt bs 0) u32 u96 bs240.val bs240.property q576 w592
    (v1_quadAt bs 152) (v1_quadAt bs 168) (v1_quadAt bs 184) (v1_quadAt bs 200)
    (v1_quadAt bs 216) (v1_quadAt bs 232) (v1_quadAt bs 248) (v1_quadAt bs 264)
    (v1_quadAt bs 280) (v1_quadAt bs 296) (v1_quadAt bs 312) (v1_quadAt bs 328)
    (v1_quadAt bs 344) (v1_quadAt bs 360) (v1_wordAt bs 376)
    (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144))
    (v1_wordAt bs 144 >>> 8)
    (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112)))
    (v1_wordAt bs 112 >>> 8)
    (v1_wordAt bs 0 ++ tag) (v1_wordAt bs 16 ++ v1_wordAt bs 8) (v1_wordAt bs 24)
    (P_heap ∗ vecU8Payload A.repAlloc u8 u16 ek ∗ vecU8Payload A.repAlloc u32 u40 dk ∗
     vecU8Payload A.repAlloc u72 pa1 rootKey ∗ vecU8Payload A.repAlloc u96 pa2 macKey ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx6_1 hx19_1 hx23_1 htr1
  refine SepWP.weaken_pre hP1' (SepWP.mono hep ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f, hvm2⟩
  refine ⟨Entails.trans hPf ?_, hvm1.trans hvm2, hsp_f, hcs_f, htr_f⟩
  rw [hx8_1, hx15_1, hx20_1, hx13_1, hx25_1, hx30_1, hx9_1, hx14_1, hx18_1, hx17_1, hx0_1,
      hx3_1, v1_zext32_setWidth8, hx27_1, hx27_hi16, hx27_hi8, hx4_1, hx5_1,
      hx21_1, v1_zext32_setWidth8, hx7_1, hx2_1, hx11_1, hx22_1, hx24_1, hx10_1,
      hx26_1, hx12_1, hx1_1, ← hu24_1152, hx28_1, hx16_1]
  have hout := v1_epilogueOutFull_entails_keysSampled A.repAlloc (F := F)
    out tag u72 pa1 u96 pa2 u8 u16 u24 u32 u40 u48 u104
    bs hbs hi32 enc P_heap hreloc ek dk rootKey macKey hek hdk hl1 hl2
    w104 w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
    bs240.val bs240.property
    (v1_wordAt bs 0 ++ tag) (v1_wordAt bs 16 ++ v1_wordAt bs 8) (v1_wordAt bs 24)
  refine Entails.trans (Entails.of_eq (show _ =
    (epilogueOutFull out
      3#64 tag (v1_wordAt bs 0) (v1_wordAt bs 8)
      (v1_wordAt bs 16) (v1_wordAt bs 24) (v1_wordAt bs 32) (v1_wordAt bs 40)
      (v1_wordAt bs 48) (v1_wordAt bs 56) (v1_wordAt bs 64) (v1_wordAt bs 72)
      ((v1_wordAt bs 80).extractLsb' 0 8) ((v1_wordAt bs 80).extractLsb' 8 32)
      ((v1_wordAt bs 80).extractLsb' 40 16) ((v1_wordAt bs 80).extractLsb' 56 8)
      (v1_wordAt bs 88) (v1_wordAt bs 96) (loByte (v1_wordAt bs 104))
      (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112)))
      (overlapWord7 (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112)))
        (v1_wordAt bs 112 >>> 8))
      (v1_wordAt bs 120)
      (((loByte (v1_wordAt bs 128)).zeroExtend 32).setWidth 8)
      (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144))
      (overlapWord7
        ((v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)).extractLsb' 64 64)
        (v1_wordAt bs 144 >>> 8))
      (v1_quadAt bs 152) (v1_quadAt bs 168) (v1_quadAt bs 184) (v1_quadAt bs 200)
      (v1_quadAt bs 216) (v1_quadAt bs 232) (v1_quadAt bs 248) (v1_quadAt bs 264)
      (v1_quadAt bs 280) (v1_quadAt bs 296) (v1_quadAt bs 312) (v1_quadAt bs 328)
      (v1_quadAt bs 344) (v1_quadAt bs 360)
      (v1_wordAt bs 376) (hi32 ++ enc.idx)
      u72 pa1 u72 u96 pa2 u96 u8 u16 u24 u32 u40 u48 u104
      w104 w112 w120
      (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
      bs240.val (v1_wordAt bs 0 ++ tag) (v1_wordAt bs 16 ++ v1_wordAt bs 8) (v1_wordAt bs 24) ∗
     P_heap ∗ vecU8Payload A.repAlloc u8 u16 ek ∗ vecU8Payload A.repAlloc u32 u40 dk ∗
     vecU8Payload A.repAlloc u72 pa1 rootKey ∗ vecU8Payload A.repAlloc u96 pa2 macKey) ∗
    A.pool lim st sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack by sep_ac_rfl)) ?_
  exact sepConj_mono_left hout

/-- Compose `+6568 -> +8180 -> s0.x30` under `Variant2aPlacedBudget.FromPbAllocHooksBudget`. -/
theorem v1_keysSampled_6568_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : Variant2aPlacedBudget.FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s : State) (out tag pa1 pa2 u8 u16 u24 u32 u40 u48 u72 u96 u104 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hi32 : BitVec 32) (enc : PolyEncoder) (P_heap : SepProp)
    (hreloc :
      ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗
        (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
        polyEncoderAt A.repAlloc (out + 8#64) enc)
    (ek dk rootKey macKey : List (BitVec 8))
    (hek : u24 = BitVec.ofNat 64 ek.length) (hdk : u48 = BitVec.ofNat 64 dk.length)
    (hl1 : u72 = BitVec.ofNat 64 rootKey.length) (hl2 : u96 = BitVec.ofNat 64 macKey.length)
    (hu24_1152 : u24 = 1152#64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 6568#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx15 : s.readReg64 .x15 = tag) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = u8) (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
        memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗ memRegion (s0.sp - 2400#64 + 240#64) 1648 ∗
        ((s0.sp - 2400#64 + 1888#64) ↦₆₄ tag) ∗ v1_encCellsAt (s0.sp - 2400#64 + 1888#64) bs ∗
        ((s0.sp - 2400#64 + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ P_heap ∗
        vecU8Payload A.repAlloc u8 u16 ek ∗ vecU8Payload A.repAlloc u32 u40 dk ∗
        vecU8Payload A.repAlloc u72 pa1 rootKey ∗ vecU8Payload A.repAlloc u96 pa2 macKey ∗
        A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out
            (.ok (.keysSampled
              { uc := { ek := ek, dk := dk, auth := { rootKey := rootKey, macKey := macKey },
                        epoch := u104 },
                sending_hdr := enc })) ∗
          A.pool lim st sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s sf ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v1_keysSampled_6568_ret_placed_of_memcpy A lim st hA.toPlacedBudget.memcpy_ok s0 s
    out tag pa1 pa2 u8 u16 u24 u32 u40 u48 u72 u96 u104 bs hbs hi32 enc P_heap hreloc
    ek dk rootKey macKey hek hdk hl1 hl2 hu24_1152 Rest
    hsp0_align hpc hrun hsp hx15 hx19 hx21 hx22 hx23 hx25 hx26 hx28 htr

theorem v1_keysSampled_6568_ret_placed_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ)
    (s0 s : State) (out tag pa1 pa2 u8 u16 u24 u32 u40 u48 u72 u96 u104 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hi32 : BitVec 32) (enc : PolyEncoder) (P_heap : SepProp)
    (hreloc :
      ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗
        (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
        polyEncoderAt A.repAlloc (out + 8#64) enc)
    (ek dk rootKey macKey : List (BitVec 8))
    (hek : u24 = BitVec.ofNat 64 ek.length) (hdk : u48 = BitVec.ofNat 64 dk.length)
    (hl1 : u72 = BitVec.ofNat 64 rootKey.length) (hl2 : u96 = BitVec.ofNat 64 macKey.length)
    (hu24_1152 : u24 = 1152#64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 6568#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx15 : s.readReg64 .x15 = tag) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = u8) (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
        memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗ memRegion (s0.sp - 2400#64 + 240#64) 1648 ∗
        ((s0.sp - 2400#64 + 1888#64) ↦₆₄ tag) ∗ v1_encCellsAt (s0.sp - 2400#64 + 1888#64) bs ∗
        ((s0.sp - 2400#64 + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ P_heap ∗
        vecU8Payload A.repAlloc u8 u16 ek ∗ vecU8Payload A.repAlloc u32 u40 dk ∗
        vecU8Payload A.repAlloc u72 pa1 rootKey ∗ vecU8Payload A.repAlloc u96 pa2 macKey ∗
        A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out
            (.ok (.keysSampled
              { uc := { ek := ek, dk := dk, auth := { rootKey := rootKey, macKey := macKey },
                        epoch := u104 },
                sending_hdr := enc })) ∗
          A.pool lim st sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s sf ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v1_keysSampled_6568_ret_placed_of_memcpy A lim st hA.memcpy_ok s0 s
    out tag pa1 pa2 u8 u16 u24 u32 u40 u48 u72 u96 u104 bs hbs hi32 enc P_heap hreloc
    ek dk rootKey macKey hek hdk hl1 hl2 hu24_1152 Rest
    hsp0_align hpc hrun hsp hx15 hx19 hx21 hx22 hx23 hx25 hx26 hx28 htr

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2ePlacedBudget
