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
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7iPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7h
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part I

Lifts the `<PolyDecoder>::from_pb = Ok(dec)` copy and staging steps (`+7404 -> +7468 -> +8180`) in
Block `333` to `VmPreserved` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7iPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States.FromPb
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved allocMemcpyVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlacedBudget
  (sessionMemcpyVmAcpSpec subroutine_ok_sessionMemcpyVmAcp_of_allocMemcpyVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
  (FromPbAllocHooksPlacedBudget)

open CryptoVerification (blkLib_333 blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

private theorem blk333_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_333.text = true := by
  decide +kernel

private theorem vmPreserved_trans_congr {s₁ s₂ s₂' s₃ : State}
    (h12 : VmPreserved s₁ s₂) (h23 : VmPreserved s₂' s₃)
    (hbs : s₂'.brkStart = s₂.brkStart := by first | rfl | simp only [wp_norm, arm64_norm])
    (hbrk : s₂'.brk = s₂.brk := by first | rfl | simp only [wp_norm, arm64_norm])
    (htp : s₂'.tpidrEl0 = s₂.tpidrEl0 := by first | rfl | simp only [wp_norm, arm64_norm])
    (hphys : s₂'.physMemAvail = s₂.physMemAvail := by first | rfl | simp only [wp_norm, arm64_norm])
    (hperm : ∀ a, s₂'.mem.perm a = s₂.mem.perm a := by
      intro _; first | rfl | simp only [wp_norm, arm64_norm])
    (hfds : LibsignalBinary.Heap.FdsHiFrame s₂ s₂' := by
      intro _ _ _; first | rfl | simp only [wp_norm, arm64_norm]) :
    VmPreserved s₁ s₃ :=
  h12.trans (VmPreserved.trans ⟨⟨hbs, hbrk, htp⟩, hphys, hperm, hfds⟩ h23)

private theorem with_vm_from {prog : Program} {target : BitVec 64} {s₀ s₁ s₁' s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (h01 : VmPreserved s₀ s₁) (h12 : VmPreserved s₁' s)
    (hk : VmPreserved s₀ s → SepWP prog target s P post)
    (hbs : s₁'.brkStart = s₁.brkStart := by first | rfl | simp only [wp_norm, arm64_norm])
    (hbrk : s₁'.brk = s₁.brk := by first | rfl | simp only [wp_norm, arm64_norm])
    (htp : s₁'.tpidrEl0 = s₁.tpidrEl0 := by first | rfl | simp only [wp_norm, arm64_norm])
    (hphys : s₁'.physMemAvail = s₁.physMemAvail := by first | rfl | simp only [wp_norm, arm64_norm])
    (hperm : ∀ a, s₁'.mem.perm a = s₁.mem.perm a := by
      intro _; first | rfl | simp only [wp_norm, arm64_norm])
    (hfds : LibsignalBinary.Heap.FdsHiFrame s₁ s₁' := by
      intro _ _ _; first | rfl | simp only [wp_norm, arm64_norm]) :
    SepWP prog target s P post :=
  hk (vmPreserved_trans_congr h01 h12 hbs hbrk htp hphys hperm hfds)

private theorem align_pre_vm {prog : Program} {target : BitVec 64} {s₀ s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (hvm : VmPreserved s₀ s)
    (hent : P ⊢ P_mid)
    (hwp : SepWP prog target s P (fun sm Pm => (Pm ⊢ P) ∧ sm = s ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid) ∧ VmPreserved s₀ sm ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨hp, hsm, hq⟩ => ⟨Entails.trans hp hent, hsm ▸ hvm, hq⟩

/-! ## 1. `<PolyDecoder>::from_pb = Ok(dec)` First Copy (`+7404 -> +7468`) -/

set_option maxHeartbeats 800000 in
/-- `VmPreserved`-strengthened placed step `+7404 -> +7468` in Block `333` under
`allocMemcpyVmSpec`: when `<PolyDecoder>::from_pb` returns `.ok dec` at `fsp + 1888..2288`
with `w0_dec.toNat < 2 ^ 63`, stores `w0_dec` to `[fsp + 120]`, `(loByte w8_dec).zeroExtend 32`
to `[fsp + 92]`, `v7_midQ128 w8_dec w16_dec w24_dec` to `[fsp + 576]` (`↦₁₂₈`),
`loBytes7 (w24_dec >>> 8)` to `[fsp + 592]`, and `memcpy`s `tail368_dec` (`368`B) from
`fsp + 1920` to `fsp + 896`, reaching `+7468` with `VmPreserved s1 sm`. -/
theorem v7_dec_ok_7404_to_7468_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_ok :
      subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsρ "memcpy") allocMemcpyVmSpec)
    (s0 s1 : State) (fsp out pbA c2 l1 w0_dec w8_dec w16_dec w24_dec w120_old w592_old : BitVec 64)
    (d92_old : BitVec 32) (q576_old : BitVec 128)
    (tail368_dec : { l : List (BitVec 8) // l.length = 368 })
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0_dec_lt : w0_dec.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 7404#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = fsp + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = fsp + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7468#64) s1
      (stackAt fsp allocHookStack ∗
        ((fsp + 92#64) ↦₃₂ d92_old) ∗
        ((fsp + 120#64) ↦₆₄ w120_old) ∗
        ((fsp + 576#64) ↦₁₂₈ q576_old) ∗
        ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592_old) ∗
        memRegion (fsp + 896#64) 368 ∗
        ((fsp + 1888#64) ↦₆₄ w0_dec) ∗
        ((fsp + 1896#64) ↦₆₄ w8_dec) ∗
        ((fsp + 1904#64) ↦₆₄ w16_dec) ∗
        ((fsp + 1912#64) ↦₆₄ w24_dec) ∗
        ((fsp + 1920#64) ↦ₛ tail368_dec.val) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          ((fsp + 92#64) ↦₃₂ (loByte w8_dec).zeroExtend 32) ∗
          ((fsp + 120#64) ↦₆₄ w0_dec) ∗
          ((fsp + 576#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) ∗
          ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 (w24_dec >>> 8)) ∗
          ((fsp + 896#64) ↦ₛ tail368_dec.val) ∗
          memRegion (fsp + 1888#64) 400 ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = fsp + 1392#64 ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  subst hsp1
  have hw0_ne := cap_add_one_beq_zero_false hw0_dec_lt
  have hmemcpy :
      subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ "memcpy") (sessionMemcpyVmAcpSpec allocHookStack) :=
    subroutine_ok_sessionMemcpyVmAcp_of_allocMemcpyVm allocHookStack hmemcpy_ok
  simp only [sessionMemcpyVmAcpSpec, sessionMemcpySpec, allocHookStack] at hmemcpy ⊢
  change s1.pc = (blkPl_333).base + 7404#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 7468#64) s1 _ _
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException (Rust.withPanics ext)))
    blkLib_eq_333 blk333_noSvc0 (mid := lsρ "memcpy")
  intro m_strip
  wp_simp_pre [pointsTo128_eq_pair64, v7_fsp_1896_triple_rest, sepConj_assoc]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_simp_pre only [v7_fsp_1905_realign_rest, sepConj_assoc]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_simp_pre only [fsp_584_realign_rest, sepConj_assoc]
  wp_step
  wp_step
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
  have hvm1 : VmPreserved s1 _ :=
    hnsp.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm1 ⊢
  have hlen368 : (368 : Nat) = tail368_dec.val.length := tail368_dec.property.symm
  wp_simp_pre only [v7_fsp_584_realign_low7_rest, hlen368, sepConj_assoc]
  wp_call hmemcpy (s1.sp + 896#64, s1.sp + 1920#64, tail368_dec.val)
  refine with_vm_from hvm1 (by assumption) fun hvm_all => ?_
  wp_simp_pre only [v7_1896_realign_final_rest, sepConj_assoc]
  refine align_pre_vm hvm_all ?_ ?_
  · have h1888_400 := v7_1888_32_368_entails_memRegion_400 s1.sp w0_dec w8_dec w16_dec w24_dec tail368_dec
    have hq576 :
        ((s1.sp + 576#64) ↦₆₄ unshiftWord w8_dec (loByte w16_dec)) ∗
        ((s1.sp + 584#64) ↦₆₄ unshiftWord w16_dec (loByte w24_dec)) =
        ((s1.sp + 576#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) := by
      unfold v7_midQ128
      rw [← v7_fsp_576_add_8 s1.sp, EncoderFromPb.pointsTo64_pair_eq_pointsTo128]
    refine Entails.trans (Entails.of_eq (show _ =
      (((s1.sp + 1888#64) ↦₆₄ w0_dec) ∗
       ((s1.sp + 1896#64) ↦₆₄ w8_dec) ∗
       ((s1.sp + 1904#64) ↦₆₄ w16_dec) ∗
       ((s1.sp + 1912#64) ↦₆₄ w24_dec) ∗
       ((s1.sp + 1920#64) ↦ₛ tail368_dec.val)) ∗
      (((s1.sp + 576#64) ↦₆₄ unshiftWord w8_dec (loByte w16_dec)) ∗
       ((s1.sp + 584#64) ↦₆₄ unshiftWord w16_dec (loByte w24_dec))) ∗
      (stackAt s1.sp 4096 ∗
       ((s1.sp + 92#64) ↦₃₂ (loByte w8_dec).zeroExtend 32) ∗
       ((s1.sp + 120#64) ↦₆₄ w0_dec) ∗
       ((s1.sp + 592#64) ↦ₛ EncoderFromPb.loBytes7 (w24_dec >>> 8)) ∗
       ((s1.sp + 896#64) ↦ₛ tail368_dec.val) ∗
       Frame) by ac_rfl)) ?_
    rw [hq576]
    exact Entails.trans (sepConj_mono_left h1888_400) (Entails.of_eq (by ac_rfl))
  · wp_done

theorem v7_dec_ok_7404_to_7468_placed_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out pbA c2 l1 w0_dec w8_dec w16_dec w24_dec w120_old w592_old : BitVec 64)
    (d92_old : BitVec 32) (q576_old : BitVec 128)
    (tail368_dec : { l : List (BitVec 8) // l.length = 368 })
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0_dec_lt : w0_dec.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 7404#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = fsp + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = fsp + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7468#64) s1
      (stackAt fsp allocHookStack ∗
        ((fsp + 92#64) ↦₃₂ d92_old) ∗
        ((fsp + 120#64) ↦₆₄ w120_old) ∗
        ((fsp + 576#64) ↦₁₂₈ q576_old) ∗
        ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592_old) ∗
        memRegion (fsp + 896#64) 368 ∗
        ((fsp + 1888#64) ↦₆₄ w0_dec) ∗
        ((fsp + 1896#64) ↦₆₄ w8_dec) ∗
        ((fsp + 1904#64) ↦₆₄ w16_dec) ∗
        ((fsp + 1912#64) ↦₆₄ w24_dec) ∗
        ((fsp + 1920#64) ↦ₛ tail368_dec.val) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          ((fsp + 92#64) ↦₃₂ (loByte w8_dec).zeroExtend 32) ∗
          ((fsp + 120#64) ↦₆₄ w0_dec) ∗
          ((fsp + 576#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) ∗
          ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 (w24_dec >>> 8)) ∗
          ((fsp + 896#64) ↦ₛ tail368_dec.val) ∗
          memRegion (fsp + 1888#64) 400 ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = fsp + 1392#64 ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) :=
  v7_dec_ok_7404_to_7468_placed hA.memcpy_ok s0 s1 fsp out pbA c2 l1
    w0_dec w8_dec w16_dec w24_dec w120_old w592_old d92_old q576_old tail368_dec Frame
    hfsp_align hw0_dec_lt hpc1 hrun1 hsp1
    hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 htr1

theorem v7_dec_ok_7404_to_7468_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out pbA c2 l1 w0_dec w8_dec w16_dec w24_dec w120_old w592_old : BitVec 64)
    (d92_old : BitVec 32) (q576_old : BitVec 128)
    (tail368_dec : { l : List (BitVec 8) // l.length = 368 })
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0_dec_lt : w0_dec.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 7404#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = fsp + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = fsp + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7468#64) s1
      (stackAt fsp allocHookStack ∗
        ((fsp + 92#64) ↦₃₂ d92_old) ∗
        ((fsp + 120#64) ↦₆₄ w120_old) ∗
        ((fsp + 576#64) ↦₁₂₈ q576_old) ∗
        ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592_old) ∗
        memRegion (fsp + 896#64) 368 ∗
        ((fsp + 1888#64) ↦₆₄ w0_dec) ∗
        ((fsp + 1896#64) ↦₆₄ w8_dec) ∗
        ((fsp + 1904#64) ↦₆₄ w16_dec) ∗
        ((fsp + 1912#64) ↦₆₄ w24_dec) ∗
        ((fsp + 1920#64) ↦ₛ tail368_dec.val) ∗
        Frame ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          ((fsp + 92#64) ↦₃₂ (loByte w8_dec).zeroExtend 32) ∗
          ((fsp + 120#64) ↦₆₄ w0_dec) ∗
          ((fsp + 576#64) ↦₁₂₈ v7_midQ128 w8_dec w16_dec w24_dec) ∗
          ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 (w24_dec >>> 8)) ∗
          ((fsp + 896#64) ↦ₛ tail368_dec.val) ∗
          memRegion (fsp + 1888#64) 400 ∗
          Frame ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = fsp + 1392#64 ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v7_dec_ok_7404_to_7468_placed hA.memcpy_ok s0 s1 fsp out pbA c2 l1
    w0_dec w8_dec w16_dec w24_dec w120_old w592_old d92_old q576_old tail368_dec
    (Frame ∗ A.pool lim st s1)
    hfsp_align hw0_dec_lt hpc1 hrun1 hsp1
    hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-! ## 2. `<PolyDecoder>::from_pb = Ok(dec)` Second Copy & Staging (`+7468 -> +8180`) -/

set_option maxHeartbeats 1600000 in
/-- `VmPreserved`-strengthened placed step `+7468 -> +8180` in Block `333` under
`allocMemcpyVmSpec`: copies `<PolyEncoder>::from_pb` `Ok` fields from `fsp + 1392..1792`,
`uc : Ct1Sent` fields from `fsp + 1264..1392`, and `dec` tail (`368`B at `fsp + 896..1264`)
into the registers and `epilogueStackSlots` expected by `states_from_pb_epilogue_8180_placed`,
with `VmPreserved s s1`. -/
theorem v7_dec_ok_7468_to_8180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_ok :
      subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsρ "memcpy") allocMemcpyVmSpec)
    (s0 s : State) (fsp out tag c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ep : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hi32 idx : BitVec 32)
    (bs328_dec : { l : List (BitVec 8) // l.length = 328 })
    (q328_dec q344_dec : BitVec 128) (w360_dec : BitVec 64)
    (w8_old w32_old w40_old w48_old w56_old w64_old w72_old w80_old w96_old w104_old w112_old
      w128_old w136_old w144_old w152_old w160_old w176_old w184_old w192_old w208_old w216_old
      w224_old w232_old w832_old w864_old w880_old w888_old w1920_old : BitVec 64)
    (d172_old : BitVec 32)
    (q608_old q624_old q640_old q656_old q672_old q688_old q704_old q720_old
      q736_old q752_old q768_old q784_old q800_old q816_old q848_old q1888_old q1904_old : BitVec 128)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 7468#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx24 : s.readReg64 .x24 = c2)
    (hx26 : s.readReg64 .x26 = l1)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s
      (stackAt fsp allocHookStack ∗
        ((fsp + 8#64) ↦₆₄ w8_old) ∗
        ((fsp + 16#64) ↦₆₄ tag) ∗
        ((fsp + 24#64) ↦₆₄ c1) ∗
        ((fsp + 32#64) ↦₆₄ w32_old) ∗
        ((fsp + 40#64) ↦₆₄ w40_old) ∗
        ((fsp + 48#64) ↦₆₄ w48_old) ∗
        ((fsp + 56#64) ↦₆₄ w56_old) ∗
        ((fsp + 64#64) ↦₆₄ w64_old) ∗
        ((fsp + 72#64) ↦₆₄ w72_old) ∗
        ((fsp + 80#64) ↦₆₄ w80_old) ∗
        ((fsp + 96#64) ↦₆₄ w96_old) ∗
        ((fsp + 104#64) ↦₆₄ w104_old) ∗
        ((fsp + 112#64) ↦₆₄ w112_old) ∗
        ((fsp + 128#64) ↦₆₄ w128_old) ∗
        ((fsp + 136#64) ↦₆₄ w136_old) ∗
        ((fsp + 144#64) ↦₆₄ w144_old) ∗
        ((fsp + 152#64) ↦₆₄ w152_old) ∗
        ((fsp + 160#64) ↦₆₄ w160_old) ∗
        ((fsp + 172#64) ↦₃₂ d172_old) ∗
        ((fsp + 176#64) ↦₆₄ w176_old) ∗
        ((fsp + 184#64) ↦₆₄ w184_old) ∗
        ((fsp + 192#64) ↦₆₄ w192_old) ∗
        ((fsp + 200#64) ↦₆₄ p1) ∗
        ((fsp + 208#64) ↦₆₄ w208_old) ∗
        ((fsp + 216#64) ↦₆₄ w216_old) ∗
        ((fsp + 224#64) ↦₆₄ w224_old) ∗
        ((fsp + 232#64) ↦₆₄ w232_old) ∗
        memRegion (fsp + 240#64) 328 ∗
        ((fsp + 608#64) ↦₁₂₈ q608_old) ∗ ((fsp + 624#64) ↦₁₂₈ q624_old) ∗
        ((fsp + 640#64) ↦₁₂₈ q640_old) ∗ ((fsp + 656#64) ↦₁₂₈ q656_old) ∗
        ((fsp + 672#64) ↦₁₂₈ q672_old) ∗ ((fsp + 688#64) ↦₁₂₈ q688_old) ∗
        ((fsp + 704#64) ↦₁₂₈ q704_old) ∗ ((fsp + 720#64) ↦₁₂₈ q720_old) ∗
        ((fsp + 736#64) ↦₁₂₈ q736_old) ∗ ((fsp + 752#64) ↦₁₂₈ q752_old) ∗
        ((fsp + 768#64) ↦₁₂₈ q768_old) ∗ ((fsp + 784#64) ↦₁₂₈ q784_old) ∗
        ((fsp + 800#64) ↦₁₂₈ q800_old) ∗ ((fsp + 816#64) ↦₁₂₈ q816_old) ∗
        ((fsp + 832#64) ↦₆₄ w832_old) ∗
        ((fsp + 848#64) ↦₁₂₈ q848_old) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864_old) ∗
        ((fsp + 880#64) ↦₆₄ w880_old) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888_old) ∗
        ((fsp + 896#64) ↦ₛ bs328_dec.val) ∗
        ((fsp + 1224#64) ↦₁₂₈ q328_dec) ∗
        ((fsp + 1240#64) ↦₁₂₈ q344_dec) ∗
        ((fsp + 1256#64) ↦₆₄ w360_dec) ∗
        v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ep ∗
        ((fsp + 1392#64) ↦₆₄ tag) ∗
        v7_encCellsAt (fsp + 1392#64) bs ∗
        ((fsp + 1784#64) ↦₆₄ (hi32 ++ idx)) ∗
        ((fsp + 1888#64) ↦₁₂₈ q1888_old) ∗
        ((fsp + 1904#64) ↦₁₂₈ q1904_old) ∗
        ((fsp + 1920#64) ↦₆₄ w1920_old) ∗
        Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt fsp allocHookStack ∗
          ((fsp + 8#64) ↦₆₄ v7_wordAt bs 128) ∗
          ((fsp + 16#64) ↦₆₄ tag) ∗
          ((fsp + 24#64) ↦₆₄ c1) ∗
          ((fsp + 32#64) ↦₆₄ ((v7_wordAt bs 88).extractLsb' 0 8).zeroExtend 64) ∗
          ((fsp + 40#64) ↦₆₄ v7_wordAt bs 40) ∗
          ((fsp + 48#64) ↦₆₄ v7_wordAt bs 96) ∗
          ((fsp + 56#64) ↦₆₄ v7_wordAt bs 0) ∗
          ((fsp + 64#64) ↦₆₄ p5) ∗
          ((fsp + 72#64) ↦₆₄ v7_wordAt bs 80) ∗
          ((fsp + 80#64) ↦₆₄ v7_wordAt bs 64) ∗
          ((fsp + 96#64) ↦₆₄ c4) ∗
          ((fsp + 104#64) ↦₆₄ l5) ∗
          ((fsp + 112#64) ↦₆₄ ep) ∗
          ((fsp + 128#64) ↦₆₄ v7_wordAt bs 72) ∗
          ((fsp + 136#64) ↦₆₄ v7_wordAt bs 32) ∗
          ((fsp + 144#64) ↦₆₄ v7_wordAt bs 56) ∗
          ((fsp + 152#64) ↦₆₄ v7_wordAt bs 48) ∗
          ((fsp + 160#64) ↦₆₄ c3) ∗
          ((fsp + 172#64) ↦₃₂ (loByte (v7_wordAt bs 136)).zeroExtend 32) ∗
          ((fsp + 176#64) ↦₆₄ l3) ∗
          ((fsp + 184#64) ↦₆₄ l2) ∗
          ((fsp + 192#64) ↦₆₄ c5) ∗
          ((fsp + 200#64) ↦₆₄ p1) ∗
          ((fsp + 208#64) ↦₆₄ v7_wordAt bs 8) ∗
          ((fsp + 216#64) ↦₆₄ v7_wordAt bs 24) ∗
          ((fsp + 224#64) ↦₆₄ p4) ∗
          ((fsp + 232#64) ↦₆₄ p2) ∗
          ((fsp + 240#64) ↦ₛ bs328_dec.val) ∗
          ((fsp + 608#64) ↦₁₂₈ v7_quadAt bs 160) ∗ ((fsp + 624#64) ↦₁₂₈ v7_quadAt bs 176) ∗
          ((fsp + 640#64) ↦₁₂₈ v7_quadAt bs 192) ∗ ((fsp + 656#64) ↦₁₂₈ v7_quadAt bs 208) ∗
          ((fsp + 672#64) ↦₁₂₈ v7_quadAt bs 224) ∗ ((fsp + 688#64) ↦₁₂₈ v7_quadAt bs 240) ∗
          ((fsp + 704#64) ↦₁₂₈ v7_quadAt bs 256) ∗ ((fsp + 720#64) ↦₁₂₈ v7_quadAt bs 272) ∗
          ((fsp + 736#64) ↦₁₂₈ v7_quadAt bs 288) ∗ ((fsp + 752#64) ↦₁₂₈ v7_quadAt bs 304) ∗
          ((fsp + 768#64) ↦₁₂₈ v7_quadAt bs 320) ∗ ((fsp + 784#64) ↦₁₂₈ v7_quadAt bs 336) ∗
          ((fsp + 800#64) ↦₁₂₈ v7_quadAt bs 352) ∗ ((fsp + 816#64) ↦₁₂₈ v7_quadAt bs 368) ∗
          ((fsp + 832#64) ↦₆₄ (hi32 ++ idx)) ∗
          ((fsp + 848#64) ↦₁₂₈ v7_midQ128 (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)) ∗
          ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v7_wordAt bs 152 >>> 8)) ∗
          ((fsp + 880#64) ↦₆₄ unshiftWord (v7_wordAt bs 112) (loByte (v7_wordAt bs 120))) ∗
          ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v7_wordAt bs 120 >>> 8)) ∗
          ((fsp + 896#64) ↦ₛ bs328_dec.val) ∗
          ((fsp + 1224#64) ↦₁₂₈ q328_dec) ∗
          ((fsp + 1240#64) ↦₁₂₈ q344_dec) ∗
          ((fsp + 1256#64) ↦₆₄ w360_dec) ∗
          v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ep ∗
          ((fsp + 1392#64) ↦₆₄ tag) ∗
          v7_encCellsAt (fsp + 1392#64) bs ∗
          ((fsp + 1784#64) ↦₆₄ (hi32 ++ idx)) ∗
          ((fsp + 1888#64) ↦₁₂₈ q328_dec) ∗
          ((fsp + 1904#64) ↦₁₂₈ q344_dec) ∗
          ((fsp + 1920#64) ↦₆₄ w360_dec) ∗
          Rest) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧
        s1.readReg64 .x6 = fsp + 576#64 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x8 = tag ∧
        s1.readReg64 .x15 = v7_wordAt bs 0 ∧
        s1.readReg64 .x20 = v7_wordAt bs 16 ∧
        s1.readReg64 .x13 = v7_wordAt bs 24 ∧
        s1.readReg64 .x25 = v7_wordAt bs 32 ∧
        s1.readReg64 .x30 = v7_wordAt bs 40 ∧
        s1.readReg64 .x9 = v7_wordAt bs 48 ∧
        s1.readReg64 .x14 = v7_wordAt bs 56 ∧
        s1.readReg64 .x18 = v7_wordAt bs 64 ∧
        s1.readReg64 .x17 = v7_wordAt bs 72 ∧
        s1.readReg64 .x0 = v7_wordAt bs 80 ∧
        s1.readReg32 .x3 = ((v7_wordAt bs 88).extractLsb' 0 8).zeroExtend 32 ∧
        s1.readReg32 .x27 = (v7_wordAt bs 88).extractLsb' 8 32 ∧
        ((s1.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = (v7_wordAt bs 88).extractLsb' 40 16 ∧
        ((s1.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = (v7_wordAt bs 88).extractLsb' 56 8 ∧
        s1.readReg64 .x4 = v7_wordAt bs 96 ∧
        s1.readReg64 .x5 = v7_wordAt bs 104 ∧
        s1.readReg32 .x21 = (loByte (v7_wordAt bs 112)).zeroExtend 32 ∧
        s1.readReg64 .x7 = v7_wordAt bs 128 ∧
        s1.readReg64 .x2 = c1 ∧
        s1.readReg64 .x11 = p1 ∧
        s1.readReg64 .x22 = l1 ∧
        s1.readReg64 .x24 = c2 ∧
        s1.readReg64 .x10 = l2 ∧
        s1.readReg64 .x26 = p3 ∧
        s1.readReg64 .x12 = l3 ∧
        s1.readReg64 .x1 = c4 ∧
        s1.readReg64 .x28 = l4 ∧
        s1.readReg64 .x16 = p5 ∧
        TraceCalleeSaved s1 s0) := by
  subst hsp
  have hmemcpy :
      subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ "memcpy") (sessionMemcpyVmAcpSpec allocHookStack) :=
    subroutine_ok_sessionMemcpyVmAcp_of_allocMemcpyVm allocHookStack hmemcpy_ok
  simp only [sessionMemcpyVmAcpSpec, sessionMemcpySpec, allocHookStack] at hmemcpy ⊢
  unfold v7_encCellsAt v7_ct1SentWordsAt
  wp_simp_pre [pointsTo128, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  change s.pc = (blkPl_333).base + 7468#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 8180#64) s _ _
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException (Rust.withPanics ext)))
    blkLib_eq_333 blk333_noSvc0 (mid := lsρ "memcpy")
  intro m_strip
  wp_conv_pre =>
    rw [v7_fsp_1488_split_rest s.sp (v7_wordAt bs 88),
        v7_fsp_1536_realign_rest s.sp (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v7_fsp_1512_realign_rest s.sp (v7_wordAt bs 112) (v7_wordAt bs 120)]
  wp_step; wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v7_fsp_880_realign_64_rest s.sp (unshiftWord (v7_wordAt bs 112) (loByte (v7_wordAt bs 120))) w888_old,
        v7_fsp_1536_unrealign_rest s.sp (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152),
        v7_fsp_1536_split_1_7_rest s.sp (v7_wordAt bs 136)]
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v7_fsp_880_unrealign_unshift_rest s.sp (v7_wordAt bs 112) (v7_wordAt bs 120),
        v7_fsp_856_realign_rest s.sp
          ((v7_midQ128 (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)).extractLsb' 64 64) w864_old]
  wp_step
  wp_conv_pre =>
    rw [v7_fsp_856_unrealign_midQ128_rest s.sp
      (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
  have hvm1 : VmPreserved s _ :=
    hnsp.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm1 ⊢
  have hlen328 : (328 : Nat) = bs328_dec.val.length := bs328_dec.property.symm
  wp_simp_pre [hlen328, sepConj_assoc]
  wp_call hmemcpy (s.sp + 240#64, s.sp + 896#64, bs328_dec.val)
  clear hlen328
  refine with_vm_from hvm1 (by assumption) fun hvm2 => ?_
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException (Rust.withPanics ext)))
    blkLib_eq_333 blk333_noSvc0 (mid := (blkPl_333).base + 8180#64)
  intro m_strip2
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real2 hnsp2 => ?_
  have hvm3 : VmPreserved _ _ :=
    hnsp2.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm3 ⊢
  have hvm_all : VmPreserved s _ := vmPreserved_trans_congr hvm2 hvm3
  refine align_pre_vm hvm_all ?_ ?_
  · rw [v7_fsp_1536_unsplit_1_7_rest s.sp (v7_wordAt bs 136),
        v7_fsp_1512_unrealign_rest s.sp (v7_wordAt bs 112) (v7_wordAt bs 120),
        v7_fsp_1488_unsplit_rest s.sp (v7_wordAt bs 88)]
    exact Entails.of_eq (by
      dsimp only [BitVec.zeroExtend]
      simp only [pointsTo128_eq_pair64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      ac_rfl)
  · wp_done

theorem v7_dec_ok_7468_to_8180_placed_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State) (fsp out tag c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ep : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hi32 idx : BitVec 32)
    (bs328_dec : { l : List (BitVec 8) // l.length = 328 })
    (q328_dec q344_dec : BitVec 128) (w360_dec : BitVec 64)
    (w8_old w32_old w40_old w48_old w56_old w64_old w72_old w80_old w96_old w104_old w112_old
      w128_old w136_old w144_old w152_old w160_old w176_old w184_old w192_old w208_old w216_old
      w224_old w232_old w832_old w864_old w880_old w888_old w1920_old : BitVec 64)
    (d172_old : BitVec 32)
    (q608_old q624_old q640_old q656_old q672_old q688_old q704_old q720_old
      q736_old q752_old q768_old q784_old q800_old q816_old q848_old q1888_old q1904_old : BitVec 128)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 7468#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx24 : s.readReg64 .x24 = c2)
    (hx26 : s.readReg64 .x26 = l1)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s
      (stackAt fsp allocHookStack ∗
        ((fsp + 8#64) ↦₆₄ w8_old) ∗
        ((fsp + 16#64) ↦₆₄ tag) ∗
        ((fsp + 24#64) ↦₆₄ c1) ∗
        ((fsp + 32#64) ↦₆₄ w32_old) ∗
        ((fsp + 40#64) ↦₆₄ w40_old) ∗
        ((fsp + 48#64) ↦₆₄ w48_old) ∗
        ((fsp + 56#64) ↦₆₄ w56_old) ∗
        ((fsp + 64#64) ↦₆₄ w64_old) ∗
        ((fsp + 72#64) ↦₆₄ w72_old) ∗
        ((fsp + 80#64) ↦₆₄ w80_old) ∗
        ((fsp + 96#64) ↦₆₄ w96_old) ∗
        ((fsp + 104#64) ↦₆₄ w104_old) ∗
        ((fsp + 112#64) ↦₆₄ w112_old) ∗
        ((fsp + 128#64) ↦₆₄ w128_old) ∗
        ((fsp + 136#64) ↦₆₄ w136_old) ∗
        ((fsp + 144#64) ↦₆₄ w144_old) ∗
        ((fsp + 152#64) ↦₆₄ w152_old) ∗
        ((fsp + 160#64) ↦₆₄ w160_old) ∗
        ((fsp + 172#64) ↦₃₂ d172_old) ∗
        ((fsp + 176#64) ↦₆₄ w176_old) ∗
        ((fsp + 184#64) ↦₆₄ w184_old) ∗
        ((fsp + 192#64) ↦₆₄ w192_old) ∗
        ((fsp + 200#64) ↦₆₄ p1) ∗
        ((fsp + 208#64) ↦₆₄ w208_old) ∗
        ((fsp + 216#64) ↦₆₄ w216_old) ∗
        ((fsp + 224#64) ↦₆₄ w224_old) ∗
        ((fsp + 232#64) ↦₆₄ w232_old) ∗
        memRegion (fsp + 240#64) 328 ∗
        ((fsp + 608#64) ↦₁₂₈ q608_old) ∗ ((fsp + 624#64) ↦₁₂₈ q624_old) ∗
        ((fsp + 640#64) ↦₁₂₈ q640_old) ∗ ((fsp + 656#64) ↦₁₂₈ q656_old) ∗
        ((fsp + 672#64) ↦₁₂₈ q672_old) ∗ ((fsp + 688#64) ↦₁₂₈ q688_old) ∗
        ((fsp + 704#64) ↦₁₂₈ q704_old) ∗ ((fsp + 720#64) ↦₁₂₈ q720_old) ∗
        ((fsp + 736#64) ↦₁₂₈ q736_old) ∗ ((fsp + 752#64) ↦₁₂₈ q752_old) ∗
        ((fsp + 768#64) ↦₁₂₈ q768_old) ∗ ((fsp + 784#64) ↦₁₂₈ q784_old) ∗
        ((fsp + 800#64) ↦₁₂₈ q800_old) ∗ ((fsp + 816#64) ↦₁₂₈ q816_old) ∗
        ((fsp + 832#64) ↦₆₄ w832_old) ∗
        ((fsp + 848#64) ↦₁₂₈ q848_old) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864_old) ∗
        ((fsp + 880#64) ↦₆₄ w880_old) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888_old) ∗
        ((fsp + 896#64) ↦ₛ bs328_dec.val) ∗
        ((fsp + 1224#64) ↦₁₂₈ q328_dec) ∗
        ((fsp + 1240#64) ↦₁₂₈ q344_dec) ∗
        ((fsp + 1256#64) ↦₆₄ w360_dec) ∗
        v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ep ∗
        ((fsp + 1392#64) ↦₆₄ tag) ∗
        v7_encCellsAt (fsp + 1392#64) bs ∗
        ((fsp + 1784#64) ↦₆₄ (hi32 ++ idx)) ∗
        ((fsp + 1888#64) ↦₁₂₈ q1888_old) ∗
        ((fsp + 1904#64) ↦₁₂₈ q1904_old) ∗
        ((fsp + 1920#64) ↦₆₄ w1920_old) ∗
        Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt fsp allocHookStack ∗
          ((fsp + 8#64) ↦₆₄ v7_wordAt bs 128) ∗
          ((fsp + 16#64) ↦₆₄ tag) ∗
          ((fsp + 24#64) ↦₆₄ c1) ∗
          ((fsp + 32#64) ↦₆₄ ((v7_wordAt bs 88).extractLsb' 0 8).zeroExtend 64) ∗
          ((fsp + 40#64) ↦₆₄ v7_wordAt bs 40) ∗
          ((fsp + 48#64) ↦₆₄ v7_wordAt bs 96) ∗
          ((fsp + 56#64) ↦₆₄ v7_wordAt bs 0) ∗
          ((fsp + 64#64) ↦₆₄ p5) ∗
          ((fsp + 72#64) ↦₆₄ v7_wordAt bs 80) ∗
          ((fsp + 80#64) ↦₆₄ v7_wordAt bs 64) ∗
          ((fsp + 96#64) ↦₆₄ c4) ∗
          ((fsp + 104#64) ↦₆₄ l5) ∗
          ((fsp + 112#64) ↦₆₄ ep) ∗
          ((fsp + 128#64) ↦₆₄ v7_wordAt bs 72) ∗
          ((fsp + 136#64) ↦₆₄ v7_wordAt bs 32) ∗
          ((fsp + 144#64) ↦₆₄ v7_wordAt bs 56) ∗
          ((fsp + 152#64) ↦₆₄ v7_wordAt bs 48) ∗
          ((fsp + 160#64) ↦₆₄ c3) ∗
          ((fsp + 172#64) ↦₃₂ (loByte (v7_wordAt bs 136)).zeroExtend 32) ∗
          ((fsp + 176#64) ↦₆₄ l3) ∗
          ((fsp + 184#64) ↦₆₄ l2) ∗
          ((fsp + 192#64) ↦₆₄ c5) ∗
          ((fsp + 200#64) ↦₆₄ p1) ∗
          ((fsp + 208#64) ↦₆₄ v7_wordAt bs 8) ∗
          ((fsp + 216#64) ↦₆₄ v7_wordAt bs 24) ∗
          ((fsp + 224#64) ↦₆₄ p4) ∗
          ((fsp + 232#64) ↦₆₄ p2) ∗
          ((fsp + 240#64) ↦ₛ bs328_dec.val) ∗
          ((fsp + 608#64) ↦₁₂₈ v7_quadAt bs 160) ∗ ((fsp + 624#64) ↦₁₂₈ v7_quadAt bs 176) ∗
          ((fsp + 640#64) ↦₁₂₈ v7_quadAt bs 192) ∗ ((fsp + 656#64) ↦₁₂₈ v7_quadAt bs 208) ∗
          ((fsp + 672#64) ↦₁₂₈ v7_quadAt bs 224) ∗ ((fsp + 688#64) ↦₁₂₈ v7_quadAt bs 240) ∗
          ((fsp + 704#64) ↦₁₂₈ v7_quadAt bs 256) ∗ ((fsp + 720#64) ↦₁₂₈ v7_quadAt bs 272) ∗
          ((fsp + 736#64) ↦₁₂₈ v7_quadAt bs 288) ∗ ((fsp + 752#64) ↦₁₂₈ v7_quadAt bs 304) ∗
          ((fsp + 768#64) ↦₁₂₈ v7_quadAt bs 320) ∗ ((fsp + 784#64) ↦₁₂₈ v7_quadAt bs 336) ∗
          ((fsp + 800#64) ↦₁₂₈ v7_quadAt bs 352) ∗ ((fsp + 816#64) ↦₁₂₈ v7_quadAt bs 368) ∗
          ((fsp + 832#64) ↦₆₄ (hi32 ++ idx)) ∗
          ((fsp + 848#64) ↦₁₂₈ v7_midQ128 (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)) ∗
          ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v7_wordAt bs 152 >>> 8)) ∗
          ((fsp + 880#64) ↦₆₄ unshiftWord (v7_wordAt bs 112) (loByte (v7_wordAt bs 120))) ∗
          ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v7_wordAt bs 120 >>> 8)) ∗
          ((fsp + 896#64) ↦ₛ bs328_dec.val) ∗
          ((fsp + 1224#64) ↦₁₂₈ q328_dec) ∗
          ((fsp + 1240#64) ↦₁₂₈ q344_dec) ∗
          ((fsp + 1256#64) ↦₆₄ w360_dec) ∗
          v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ep ∗
          ((fsp + 1392#64) ↦₆₄ tag) ∗
          v7_encCellsAt (fsp + 1392#64) bs ∗
          ((fsp + 1784#64) ↦₆₄ (hi32 ++ idx)) ∗
          ((fsp + 1888#64) ↦₁₂₈ q328_dec) ∗
          ((fsp + 1904#64) ↦₁₂₈ q344_dec) ∗
          ((fsp + 1920#64) ↦₆₄ w360_dec) ∗
          Rest) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧
        s1.readReg64 .x6 = fsp + 576#64 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x8 = tag ∧
        s1.readReg64 .x15 = v7_wordAt bs 0 ∧
        s1.readReg64 .x20 = v7_wordAt bs 16 ∧
        s1.readReg64 .x13 = v7_wordAt bs 24 ∧
        s1.readReg64 .x25 = v7_wordAt bs 32 ∧
        s1.readReg64 .x30 = v7_wordAt bs 40 ∧
        s1.readReg64 .x9 = v7_wordAt bs 48 ∧
        s1.readReg64 .x14 = v7_wordAt bs 56 ∧
        s1.readReg64 .x18 = v7_wordAt bs 64 ∧
        s1.readReg64 .x17 = v7_wordAt bs 72 ∧
        s1.readReg64 .x0 = v7_wordAt bs 80 ∧
        s1.readReg32 .x3 = ((v7_wordAt bs 88).extractLsb' 0 8).zeroExtend 32 ∧
        s1.readReg32 .x27 = (v7_wordAt bs 88).extractLsb' 8 32 ∧
        ((s1.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = (v7_wordAt bs 88).extractLsb' 40 16 ∧
        ((s1.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = (v7_wordAt bs 88).extractLsb' 56 8 ∧
        s1.readReg64 .x4 = v7_wordAt bs 96 ∧
        s1.readReg64 .x5 = v7_wordAt bs 104 ∧
        s1.readReg32 .x21 = (loByte (v7_wordAt bs 112)).zeroExtend 32 ∧
        s1.readReg64 .x7 = v7_wordAt bs 128 ∧
        s1.readReg64 .x2 = c1 ∧
        s1.readReg64 .x11 = p1 ∧
        s1.readReg64 .x22 = l1 ∧
        s1.readReg64 .x24 = c2 ∧
        s1.readReg64 .x10 = l2 ∧
        s1.readReg64 .x26 = p3 ∧
        s1.readReg64 .x12 = l3 ∧
        s1.readReg64 .x1 = c4 ∧
        s1.readReg64 .x28 = l4 ∧
        s1.readReg64 .x16 = p5 ∧
        TraceCalleeSaved s1 s0) :=
  v7_dec_ok_7468_to_8180_placed hA.memcpy_ok s0 s fsp out tag c1 p1 l1 c2 p2 l2 c3 p3 l3
    c4 p4 l4 c5 p5 l5 ep bs hbs hi32 idx bs328_dec q328_dec q344_dec w360_dec
    w8_old w32_old w40_old w48_old w56_old w64_old w72_old w80_old w96_old w104_old w112_old
    w128_old w136_old w144_old w152_old w160_old w176_old w184_old w192_old w208_old w216_old
    w224_old w232_old w832_old w864_old w880_old w888_old w1920_old d172_old
    q608_old q624_old q640_old q656_old q672_old q688_old q704_old q720_old
    q736_old q752_old q768_old q784_old q800_old q816_old q848_old q1888_old q1904_old
    Rest hfsp_align hpc hrun hsp hx19 hx21 hx24 hx26 htr

theorem v7_dec_ok_7468_to_8180_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State) (fsp out tag c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ep : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hi32 idx : BitVec 32)
    (bs328_dec : { l : List (BitVec 8) // l.length = 328 })
    (q328_dec q344_dec : BitVec 128) (w360_dec : BitVec 64)
    (w8_old w32_old w40_old w48_old w56_old w64_old w72_old w80_old w96_old w104_old w112_old
      w128_old w136_old w144_old w152_old w160_old w176_old w184_old w192_old w208_old w216_old
      w224_old w232_old w832_old w864_old w880_old w888_old w1920_old : BitVec 64)
    (d172_old : BitVec 32)
    (q608_old q624_old q640_old q656_old q672_old q688_old q704_old q720_old
      q736_old q752_old q768_old q784_old q800_old q816_old q848_old q1888_old q1904_old : BitVec 128)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 7468#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx24 : s.readReg64 .x24 = c2)
    (hx26 : s.readReg64 .x26 = l1)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s
      (stackAt fsp allocHookStack ∗
        ((fsp + 8#64) ↦₆₄ w8_old) ∗
        ((fsp + 16#64) ↦₆₄ tag) ∗
        ((fsp + 24#64) ↦₆₄ c1) ∗
        ((fsp + 32#64) ↦₆₄ w32_old) ∗
        ((fsp + 40#64) ↦₆₄ w40_old) ∗
        ((fsp + 48#64) ↦₆₄ w48_old) ∗
        ((fsp + 56#64) ↦₆₄ w56_old) ∗
        ((fsp + 64#64) ↦₆₄ w64_old) ∗
        ((fsp + 72#64) ↦₆₄ w72_old) ∗
        ((fsp + 80#64) ↦₆₄ w80_old) ∗
        ((fsp + 96#64) ↦₆₄ w96_old) ∗
        ((fsp + 104#64) ↦₆₄ w104_old) ∗
        ((fsp + 112#64) ↦₆₄ w112_old) ∗
        ((fsp + 128#64) ↦₆₄ w128_old) ∗
        ((fsp + 136#64) ↦₆₄ w136_old) ∗
        ((fsp + 144#64) ↦₆₄ w144_old) ∗
        ((fsp + 152#64) ↦₆₄ w152_old) ∗
        ((fsp + 160#64) ↦₆₄ w160_old) ∗
        ((fsp + 172#64) ↦₃₂ d172_old) ∗
        ((fsp + 176#64) ↦₆₄ w176_old) ∗
        ((fsp + 184#64) ↦₆₄ w184_old) ∗
        ((fsp + 192#64) ↦₆₄ w192_old) ∗
        ((fsp + 200#64) ↦₆₄ p1) ∗
        ((fsp + 208#64) ↦₆₄ w208_old) ∗
        ((fsp + 216#64) ↦₆₄ w216_old) ∗
        ((fsp + 224#64) ↦₆₄ w224_old) ∗
        ((fsp + 232#64) ↦₆₄ w232_old) ∗
        memRegion (fsp + 240#64) 328 ∗
        ((fsp + 608#64) ↦₁₂₈ q608_old) ∗ ((fsp + 624#64) ↦₁₂₈ q624_old) ∗
        ((fsp + 640#64) ↦₁₂₈ q640_old) ∗ ((fsp + 656#64) ↦₁₂₈ q656_old) ∗
        ((fsp + 672#64) ↦₁₂₈ q672_old) ∗ ((fsp + 688#64) ↦₁₂₈ q688_old) ∗
        ((fsp + 704#64) ↦₁₂₈ q704_old) ∗ ((fsp + 720#64) ↦₁₂₈ q720_old) ∗
        ((fsp + 736#64) ↦₁₂₈ q736_old) ∗ ((fsp + 752#64) ↦₁₂₈ q752_old) ∗
        ((fsp + 768#64) ↦₁₂₈ q768_old) ∗ ((fsp + 784#64) ↦₁₂₈ q784_old) ∗
        ((fsp + 800#64) ↦₁₂₈ q800_old) ∗ ((fsp + 816#64) ↦₁₂₈ q816_old) ∗
        ((fsp + 832#64) ↦₆₄ w832_old) ∗
        ((fsp + 848#64) ↦₁₂₈ q848_old) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864_old) ∗
        ((fsp + 880#64) ↦₆₄ w880_old) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888_old) ∗
        ((fsp + 896#64) ↦ₛ bs328_dec.val) ∗
        ((fsp + 1224#64) ↦₁₂₈ q328_dec) ∗
        ((fsp + 1240#64) ↦₁₂₈ q344_dec) ∗
        ((fsp + 1256#64) ↦₆₄ w360_dec) ∗
        v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ep ∗
        ((fsp + 1392#64) ↦₆₄ tag) ∗
        v7_encCellsAt (fsp + 1392#64) bs ∗
        ((fsp + 1784#64) ↦₆₄ (hi32 ++ idx)) ∗
        ((fsp + 1888#64) ↦₁₂₈ q1888_old) ∗
        ((fsp + 1904#64) ↦₁₂₈ q1904_old) ∗
        ((fsp + 1920#64) ↦₆₄ w1920_old) ∗
        Rest ∗ A.pool lim st s)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt fsp allocHookStack ∗
          ((fsp + 8#64) ↦₆₄ v7_wordAt bs 128) ∗
          ((fsp + 16#64) ↦₆₄ tag) ∗
          ((fsp + 24#64) ↦₆₄ c1) ∗
          ((fsp + 32#64) ↦₆₄ ((v7_wordAt bs 88).extractLsb' 0 8).zeroExtend 64) ∗
          ((fsp + 40#64) ↦₆₄ v7_wordAt bs 40) ∗
          ((fsp + 48#64) ↦₆₄ v7_wordAt bs 96) ∗
          ((fsp + 56#64) ↦₆₄ v7_wordAt bs 0) ∗
          ((fsp + 64#64) ↦₆₄ p5) ∗
          ((fsp + 72#64) ↦₆₄ v7_wordAt bs 80) ∗
          ((fsp + 80#64) ↦₆₄ v7_wordAt bs 64) ∗
          ((fsp + 96#64) ↦₆₄ c4) ∗
          ((fsp + 104#64) ↦₆₄ l5) ∗
          ((fsp + 112#64) ↦₆₄ ep) ∗
          ((fsp + 128#64) ↦₆₄ v7_wordAt bs 72) ∗
          ((fsp + 136#64) ↦₆₄ v7_wordAt bs 32) ∗
          ((fsp + 144#64) ↦₆₄ v7_wordAt bs 56) ∗
          ((fsp + 152#64) ↦₆₄ v7_wordAt bs 48) ∗
          ((fsp + 160#64) ↦₆₄ c3) ∗
          ((fsp + 172#64) ↦₃₂ (loByte (v7_wordAt bs 136)).zeroExtend 32) ∗
          ((fsp + 176#64) ↦₆₄ l3) ∗
          ((fsp + 184#64) ↦₆₄ l2) ∗
          ((fsp + 192#64) ↦₆₄ c5) ∗
          ((fsp + 200#64) ↦₆₄ p1) ∗
          ((fsp + 208#64) ↦₆₄ v7_wordAt bs 8) ∗
          ((fsp + 216#64) ↦₆₄ v7_wordAt bs 24) ∗
          ((fsp + 224#64) ↦₆₄ p4) ∗
          ((fsp + 232#64) ↦₆₄ p2) ∗
          ((fsp + 240#64) ↦ₛ bs328_dec.val) ∗
          ((fsp + 608#64) ↦₁₂₈ v7_quadAt bs 160) ∗ ((fsp + 624#64) ↦₁₂₈ v7_quadAt bs 176) ∗
          ((fsp + 640#64) ↦₁₂₈ v7_quadAt bs 192) ∗ ((fsp + 656#64) ↦₁₂₈ v7_quadAt bs 208) ∗
          ((fsp + 672#64) ↦₁₂₈ v7_quadAt bs 224) ∗ ((fsp + 688#64) ↦₁₂₈ v7_quadAt bs 240) ∗
          ((fsp + 704#64) ↦₁₂₈ v7_quadAt bs 256) ∗ ((fsp + 720#64) ↦₁₂₈ v7_quadAt bs 272) ∗
          ((fsp + 736#64) ↦₁₂₈ v7_quadAt bs 288) ∗ ((fsp + 752#64) ↦₁₂₈ v7_quadAt bs 304) ∗
          ((fsp + 768#64) ↦₁₂₈ v7_quadAt bs 320) ∗ ((fsp + 784#64) ↦₁₂₈ v7_quadAt bs 336) ∗
          ((fsp + 800#64) ↦₁₂₈ v7_quadAt bs 352) ∗ ((fsp + 816#64) ↦₁₂₈ v7_quadAt bs 368) ∗
          ((fsp + 832#64) ↦₆₄ (hi32 ++ idx)) ∗
          ((fsp + 848#64) ↦₁₂₈ v7_midQ128 (v7_wordAt bs 136) (v7_wordAt bs 144) (v7_wordAt bs 152)) ∗
          ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v7_wordAt bs 152 >>> 8)) ∗
          ((fsp + 880#64) ↦₆₄ unshiftWord (v7_wordAt bs 112) (loByte (v7_wordAt bs 120))) ∗
          ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v7_wordAt bs 120 >>> 8)) ∗
          ((fsp + 896#64) ↦ₛ bs328_dec.val) ∗
          ((fsp + 1224#64) ↦₁₂₈ q328_dec) ∗
          ((fsp + 1240#64) ↦₁₂₈ q344_dec) ∗
          ((fsp + 1256#64) ↦₆₄ w360_dec) ∗
          v7_ct1SentWordsAt (fsp + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ep ∗
          ((fsp + 1392#64) ↦₆₄ tag) ∗
          v7_encCellsAt (fsp + 1392#64) bs ∗
          ((fsp + 1784#64) ↦₆₄ (hi32 ++ idx)) ∗
          ((fsp + 1888#64) ↦₁₂₈ q328_dec) ∗
          ((fsp + 1904#64) ↦₁₂₈ q344_dec) ∗
          ((fsp + 1920#64) ↦₆₄ w360_dec) ∗
          Rest ∗ A.pool lim st s1) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧
        s1.readReg64 .x6 = fsp + 576#64 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x8 = tag ∧
        s1.readReg64 .x15 = v7_wordAt bs 0 ∧
        s1.readReg64 .x20 = v7_wordAt bs 16 ∧
        s1.readReg64 .x13 = v7_wordAt bs 24 ∧
        s1.readReg64 .x25 = v7_wordAt bs 32 ∧
        s1.readReg64 .x30 = v7_wordAt bs 40 ∧
        s1.readReg64 .x9 = v7_wordAt bs 48 ∧
        s1.readReg64 .x14 = v7_wordAt bs 56 ∧
        s1.readReg64 .x18 = v7_wordAt bs 64 ∧
        s1.readReg64 .x17 = v7_wordAt bs 72 ∧
        s1.readReg64 .x0 = v7_wordAt bs 80 ∧
        s1.readReg32 .x3 = ((v7_wordAt bs 88).extractLsb' 0 8).zeroExtend 32 ∧
        s1.readReg32 .x27 = (v7_wordAt bs 88).extractLsb' 8 32 ∧
        ((s1.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = (v7_wordAt bs 88).extractLsb' 40 16 ∧
        ((s1.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = (v7_wordAt bs 88).extractLsb' 56 8 ∧
        s1.readReg64 .x4 = v7_wordAt bs 96 ∧
        s1.readReg64 .x5 = v7_wordAt bs 104 ∧
        s1.readReg32 .x21 = (loByte (v7_wordAt bs 112)).zeroExtend 32 ∧
        s1.readReg64 .x7 = v7_wordAt bs 128 ∧
        s1.readReg64 .x2 = c1 ∧
        s1.readReg64 .x11 = p1 ∧
        s1.readReg64 .x22 = l1 ∧
        s1.readReg64 .x24 = c2 ∧
        s1.readReg64 .x10 = l2 ∧
        s1.readReg64 .x26 = p3 ∧
        s1.readReg64 .x12 = l3 ∧
        s1.readReg64 .x1 = c4 ∧
        s1.readReg64 .x28 = l4 ∧
        s1.readReg64 .x16 = p5 ∧
        TraceCalleeSaved s1 s0) := by
  have hwp := v7_dec_ok_7468_to_8180_placed hA.memcpy_ok s0 s fsp out tag c1 p1 l1 c2 p2 l2 c3 p3 l3
    c4 p4 l4 c5 p5 l5 ep bs hbs hi32 idx bs328_dec q328_dec q344_dec w360_dec
    w8_old w32_old w40_old w48_old w56_old w64_old w72_old w80_old w96_old w104_old w112_old
    w128_old w136_old w144_old w152_old w160_old w176_old w184_old w192_old w208_old w216_old
    w224_old w232_old w832_old w864_old w880_old w888_old w1920_old d172_old
    q608_old q624_old q640_old q656_old q672_old q688_old q704_old q720_old
    q736_old q752_old q768_old q784_old q800_old q816_old q848_old q1888_old q1904_old
    (Rest ∗ A.pool lim st s) hfsp_align hpc hrun hsp hx19 hx21 hx24 hx26 htr
  refine SepWP.mono hwp fun s1 P1 _ _ ⟨hP1, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP1
  exact ⟨hP1, hvm, hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7iPlacedBudget
