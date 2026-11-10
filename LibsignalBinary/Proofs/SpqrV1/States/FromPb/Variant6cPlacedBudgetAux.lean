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
public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6bPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6cPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6c
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Auxiliary `Authenticator` Clone Helpers for `Variant6cPlacedBudget`

Relocatable Variant 6 (`HeaderReceived`, Block `333`) cold OOM panic helpers (`+11596`, `+11620`)
and total-correctness `ProtoAuthenticator` buffer clone steps (`+3796 -> +8812 -> +9852`) under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6cPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.RustHeap (allocFailedEvent allocFailedIn allocHookStack)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym spqr_externAt?_of_mem)
open CryptoVerification.SpqrV1.Drop (vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved ofNat_beq_zero_false stackAt_encoderFromPb_split_allocHook statesFromPbOnPanic
   v1_bv_add_add_lit v1_bv_sub_sub_lit v1_shl8_extract_0_8
   vecU8Payload_of_nil vecU8Payload_pos vecU8Payload_pos_dealloc vecU8Payload_pos_unpack)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload vecU8Payload_entails_dealloc)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget
   RustLayoutOk VmPreserved rustAllocEvents rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget (authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (FromPbAllocHooksPlacedBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2 (seq_clean_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (blk333_noSvc0 entails_pre_st)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_sub_sub_lit v1_shl8_extract_0_8 v1_bv_add_add_lit

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

/-! ## 1. `SepWPp` OOM Cold Panic Helpers (`+11596` and `+11620`) -/

private theorem allocFailedIn_and_prefix_of_eq {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn
  rw [h]
  exact ⟨by simp, List.prefix_append _ _⟩

/-- Shared OOM cold path at `+11596` under an explicit `handle_error` panic hook hypothesis. -/
theorem v6hr_oom_11596_entails_of_panic_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hpanic_ok : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (s0 s : State) (target_pc : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11596#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => P_f ⊢ statesFromPbOnPanic s0 sf) := by
  have hpanic :
      ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)).externAt?
        (lsρ spqrHandleErrorSym) = some Rust.panicked :=
    Eq.trans spqr_externAt?_of_mem hpanic_ok
  change s.pc = (blkPl_333).base + 11596#64 at hpc
  change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s P Q _
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
  unfold statesFromPbOnPanic
  exact Entails.pure_right
    (allocFailedIn_and_prefix_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *]))
    (entails_anyHeap _)

theorem v6hr_oom_11596_entails_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State) (target_pc : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11596#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => P_f ⊢ statesFromPbOnPanic s0 sf) :=
  v6hr_oom_11596_entails_of_panic_placed hA.panic_ok s0 s target_pc P Q hpc hrun htr

theorem v6hr_oom_11596_entails_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s : State) (target_pc : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11596#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => P_f ⊢ statesFromPbOnPanic s0 sf) :=
  v6hr_oom_11596_entails_of_panic_placed hA.panic_ok s0 s target_pc P Q hpc hrun htr

/-- Shared OOM cold path at `+11620` under an explicit `handle_error` panic hook hypothesis. -/
theorem v6hr_oom_11620_entails_of_panic_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hpanic_ok : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (s0 s : State) (target_pc : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11620#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => P_f ⊢ statesFromPbOnPanic s0 sf) := by
  have hpanic :
      ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)).externAt?
        (lsρ spqrHandleErrorSym) = some Rust.panicked :=
    Eq.trans spqr_externAt?_of_mem hpanic_ok
  change s.pc = (blkPl_333).base + 11620#64 at hpc
  change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s P Q _
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
  unfold statesFromPbOnPanic
  exact Entails.pure_right
    (allocFailedIn_and_prefix_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *]))
    (entails_anyHeap _)

theorem v6hr_oom_11620_entails_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State) (target_pc : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11620#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => P_f ⊢ statesFromPbOnPanic s0 sf) :=
  v6hr_oom_11620_entails_of_panic_placed hA.panic_ok s0 s target_pc P Q hpc hrun htr

theorem v6hr_oom_11620_entails_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s : State) (target_pc : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11620#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => P_f ⊢ statesFromPbOnPanic s0 sf) :=
  v6hr_oom_11620_entails_of_panic_placed hA.panic_ok s0 s target_pc P Q hpc hrun htr

/-! ## 2. Total-Correctness `Authenticator` Buffer Clones (`+3796 -> +8812` and `+8812 -> +9852`) -/

/-- Clones `authPb.rootKey` at `+3796 -> +8812` under
    `FitsEvents M lim st (authKeyCloneEvents rootKey)` without panic or OOM:
    stores `p2` at `[fsp + 208]`, `ep` at `[fsp + 128]`, `p0` at `[fsp + 144]`, `d116` at
    `[fsp + 200]`, and `p1_new` at `[fsp + 192]`, producing
    `vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey` and weakening the
    original buffer to `vecCapPtrDealloc A.repAlloc c1 p1`. -/
theorem v6hr_clone_rootKey_3796_to_8812_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State)
    (out c0 p0 c1 p1 c2 p2 l2 ep c3 l3 w120 v128 v144 v192 v208 : BitVec 64)
    (d112 d116 d184 d200 : BitVec 32) (rootKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents rootKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3796#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = ep)
    (hx9_1 : s1.readReg64 .x9 = p0)
    (hx11_1 : s1.readReg64 .x11 = d112.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d116.zeroExtend 64)
    (_hx13_1 : s1.readReg64 .x13 = w120)
    (hx14_1 : s1.readReg64 .x14 = p2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = c0)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 rootKey.length)
    (hx23_1 : s1.readReg64 .x23 = l3)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = l2)
    (hx26_1 : s1.readReg64 .x26 = p1)
    (hx28_1 : s1.readReg64 .x28 = c3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8812#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 128#64) ↦₆₄ v128) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ v144) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ v192) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₃₂ d200) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ v208) ∗
        vecU8Payload A.repAlloc c1 p1 rootKey ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ (p1_new : BitVec 64) (d184' : BitVec 32),
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 128#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184') ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗
            (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecCapPtrDealloc A.repAlloc c1 p1 ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents rootKey) st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
          sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = c0 ∧ sm.readReg64 .x21 = c2 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 rootKey.length ∧ sm.readReg64 .x23 = l3 ∧
          sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = l2 ∧ sm.readReg64 .x26 = p1 ∧
          sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  generalize hfsp_eq : s0.sp - 2400#64 = fsp at hfsp_align hsp1 ⊢
  clear hfsp_eq hsp0_align
  have hr_cases : rootKey = [] ∨ 0 < rootKey.length := by cases rootKey <;> simp
  rcases hr_cases with hr_nil | hr_pos
  · have hevs : authKeyCloneEvents rootKey = [] := by simp [authKeyCloneEvents, hr_nil]
    rw [hevs, M.stepEvents_nil]
    rw [hr_nil] at hx22_1 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx22_1 ⊢
    refine SepWP.mono
      (post := fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 128#64) ↦₆₄ ep) ∗ ((fsp + 144#64) ↦₆₄ p0) ∗
          ((fsp + 184#64) ↦₃₂ d184) ∗ ((fsp + 192#64) ↦₆₄ 1#64) ∗
          ((fsp + 200#64) ↦₃₂ d116) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
          vecU8Payload A.repAlloc 0#64 1#64 [] ∗
          vecCapPtrDealloc A.repAlloc c1 p1 ∗
          A.pool lim st sm ∗ Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = c0 ∧ sm.readReg64 .x21 = c2 ∧
        sm.readReg64 .x22 = 0#64 ∧ sm.readReg64 .x23 = l3 ∧
        sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = l2 ∧ sm.readReg64 .x26 = p1 ∧
        sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0)
      ?_
      fun _ _ _ _ ⟨hPm, hregs⟩ => ⟨1#64, d184, hPm, hregs⟩
    refine seq_clean_st
      (mid := lsmpl.base 333 + 8804#64)
      (P_mid := fun sm =>
        stackAt fsp encoderFromPbStack ∗
        ((fsp + 128#64) ↦₆₄ ep) ∗ ((fsp + 144#64) ↦₆₄ p0) ∗
        ((fsp + 184#64) ↦₃₂ d184) ∗ ((fsp + 192#64) ↦₆₄ v192) ∗
        ((fsp + 200#64) ↦₃₂ d116) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗
        A.pool lim st sm ∗ Rest)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = c0 ∧ sm.readReg64 .x21 = c2 ∧
        sm.readReg64 .x22 = 0#64 ∧ sm.readReg64 .x23 = l3 ∧
        sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = l2 ∧ sm.readReg64 .x26 = p1 ∧
        sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · change s1.pc = (blkPl_333).base + 3796#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 8804#64) s1 _ _
      wp_steps_sync_333 ((blkPl_333).base + 8804#64)
      simp only [State.setMem_setMem]
      have hd := vecU8Payload_entails_dealloc A.repAlloc c1 p1 []
      refine entails_pre_st ?_ ?_
      · intro sc hsc; rw [← hsc]
        refine Entails.trans (Entails.of_eq (show _ =
          vecU8Payload A.repAlloc c1 p1 [] ∗
          (stackAt fsp encoderFromPbStack ∗
           ((fsp + 128#64) ↦₆₄ ep) ∗ ((fsp + 144#64) ↦₆₄ p0) ∗
           ((fsp + 184#64) ↦₃₂ d184) ∗ ((fsp + 192#64) ↦₆₄ v192) ∗
           ((fsp + 200#64) ↦₃₂ d116) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
           A.pool lim st sc ∗ Rest) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hd) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx11_2, hx12_2, hx19_2, hx20_2, hx21_2, hx22_2,
        hx23_2, hx24_2, hx25_2, hx26_2, hx28_2, htr2⟩
      change s2.pc = (blkPl_333).base + 8804#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 8812#64) s2 _ _
      wp_steps_sync_333 ((blkPl_333).base + 8812#64)
      simp only [State.setMem_setMem]
      have hn := vecU8Payload_of_nil A.repAlloc
      dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
      refine entails_pre_st ?_ ?_
      · intro sc hsc; rw [← hsc]
        refine Entails.trans (Entails.of_eq (show _ =
          emp ∗
          (stackAt fsp encoderFromPbStack ∗
           ((fsp + 128#64) ↦₆₄ ep) ∗ ((fsp + 144#64) ↦₆₄ p0) ∗
           ((fsp + 184#64) ↦₃₂ d184) ∗ ((fsp + 192#64) ↦₆₄ 1#64) ∗
           ((fsp + 200#64) ↦₃₂ d116) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
           vecCapPtrDealloc A.repAlloc c1 p1 ∗
           A.pool lim st sc ∗ Rest) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hn) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
  · have hne_nil : rootKey.isEmpty = false := by
      cases h : rootKey with | nil => simp [h] at hr_pos | cons => rfl
    have hevs : authKeyCloneEvents rootKey = rustAllocEvents rootKey.length 1 := by
      simp [authKeyCloneEvents, hne_nil]
    rw [hevs] at hfits ⊢
    refine SepWP.weaken_pre (Entails.trans
      (Entails.of_eq (show _ =
        vecU8Payload A.repAlloc c1 p1 rootKey ∗
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 128#64) ↦₆₄ v128) ∗ ((fsp + 144#64) ↦₆₄ v144) ∗
         ((fsp + 184#64) ↦₃₂ d184) ∗ ((fsp + 192#64) ↦₆₄ v192) ∗
         ((fsp + 200#64) ↦₃₂ d200) ∗ ((fsp + 208#64) ↦₆₄ v208) ∗
         A.pool lim st s1 ∗ Rest) by sep_ac_rfl))
      (Entails.trans
        (sepConj_mono_left (vecU8Payload_pos_unpack A.repAlloc c1 p1 rootKey hr_pos))
        (Entails.of_eq (show _ =
          ⌜rootKey.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63 ∧ p1 ≠ 0#64 ∧ c1 ≠ 0#64⌝ ∗
          (memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
           ((fsp + 128#64) ↦₆₄ v128) ∗ ((fsp + 144#64) ↦₆₄ v144) ∗
           ((fsp + 184#64) ↦₃₂ d184) ∗ ((fsp + 192#64) ↦₆₄ v192) ∗
           ((fsp + 200#64) ↦₃₂ d200) ∗ ((fsp + 208#64) ↦₆₄ v208) ∗
           A.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
           memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length) ∗
           A.pool lim st s1 ∗ Rest) by
          rw [stackAt_encoderFromPb_split_allocHook fsp]
          dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
          sep_ac_rfl)))) ?_
    apply SepWP.pure_elim
    rintro ⟨hr_le, hr_cap, hp1_ne, hc1_ne⟩
    have hr_lt63 : rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : rootKey.length < 2 ^ 64 := by omega
    have hr_toNat : (BitVec.ofNat 64 rootKey.length).toNat = rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hr_ne0 : (BitVec.ofNat 64 rootKey.length == 0#64) = false :=
      ofNat_beq_zero_false hr_pos hr_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hrlay : RustLayoutOk rootKey.length 1 := ⟨⟨hr_pos, hpow1, hr_lt63⟩, by decide⟩
    have hshim := hA.shim_ok
    dsimp only [rustAllocShimVmSpec] at hshim
    have halloc := subroutine_ok_allocNoOom_of_budget hA.alloc_ok
    dsimp only [rustCliAllocNoOomSpec] at halloc
    have hmc := hA.memcpy_ok
    dsimp only [allocMemcpyVmSpec] at hmc
    clear hA
    change s1.pc = (blkPl_333).base + 3796#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8812#64) s1 _ _
    wp_steps_sync_333 (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp_shim : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_333 (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (rootKey.length, 1, st)
    have hoom0 : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
    have hoom0_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_false_of_ne hoom0
    have hacp_alloc : AllocCallPreserved s1 sf_1 :=
      hacp_shim.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
    wp_steps_sync_333 (lsρ "memcpy")
    simp only [State.setMem_setMem]
    wp_call hmc (sf_1.readReg64 .x0, p1, rootKey)
    have hacp_mc : AllocCallPreserved s1 sf_2 :=
      hacp_alloc.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_2›)
    have hsp_sf : sf.sp = fsp := by simp only [wp_norm, arm64_norm, *]
    have hsp_sf1 : sf_1.sp = fsp := by simp only [wp_norm, arm64_norm, *]
    have hsp_sf2 : sf_2.sp = fsp := by simp only [wp_norm, arm64_norm, *]
    have htr_sf2 : sf_2.trace = s0.trace := hacp_mc.2.1.trans htr1.1
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 := by
      simp only [wp_norm, arm64_norm, htr1.2, *]
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    refine SepWP.mono
      (post := fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 128#64) ↦₆₄ ep) ∗ ((fsp + 144#64) ↦₆₄ p0) ∗
          ((fsp + 184#64) ↦₃₂ d112) ∗ ((fsp + 192#64) ↦₆₄ sf_1.readReg64 .x0) ∗
          ((fsp + 200#64) ↦₃₂ d116) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length)
            (sf_1.readReg64 .x0) rootKey ∗
          vecCapPtrDealloc A.repAlloc c1 p1 ∗
          A.pool lim (M.stepEvents (rustAllocEvents rootKey.length 1) st) sm ∗ Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = c0 ∧ sm.readReg64 .x21 = c2 ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 rootKey.length ∧ sm.readReg64 .x23 = l3 ∧
        sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = l2 ∧ sm.readReg64 .x26 = p1 ∧
        sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0)
      ?_
      fun _ _ _ _ ⟨hPm, hregs⟩ => ⟨sf_1.readReg64 .x0, d112, hPm, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 8812#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_pos_dealloc A.repAlloc c1 p1 rootKey hr_le hr_cap hp1_ne hc1_ne
    have hp := vecU8Payload_pos A.repAlloc (sf_1.readReg64 .x0) rootKey hr_pos hr_lt63 hoom0
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc, stackAt_encoderFromPb_split_allocHook fsp]
      simp only [hsp_sf, hsp_sf1, hsp_sf2]
      refine Entails.trans (Entails.of_eq (show _ =
        (A.repAlloc.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
         memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length)) ∗
        (A.repAlloc.live (sf_1.readReg64 .x0) rootKey.length 1 ∗
         (sf_1.readReg64 .x0 ↦ₛ rootKey)) ∗
        (memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
         ((fsp + 128#64) ↦₆₄ ep) ∗ ((fsp + 144#64) ↦₆₄ p0) ∗
         ((fsp + 184#64) ↦₃₂ d112) ∗ ((fsp + 192#64) ↦₆₄ sf_1.readReg64 .x0) ∗
         ((fsp + 200#64) ↦₃₂ d116) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
         A.pool lim (M.stepEvents (rustAllocEvents rootKey.length 1) st) sc ∗ Rest) by
        dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

theorem v6hr_clone_rootKey_3796_to_8812_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State)
    (out c0 p0 c1 p1 c2 p2 l2 ep c3 l3 w120 v128 v144 v192 v208 : BitVec 64)
    (d112 d116 d184 d200 : BitVec 32) (rootKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents rootKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3796#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = ep)
    (hx9_1 : s1.readReg64 .x9 = p0)
    (hx11_1 : s1.readReg64 .x11 = d112.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d116.zeroExtend 64)
    (hx13_1 : s1.readReg64 .x13 = w120)
    (hx14_1 : s1.readReg64 .x14 = p2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = c0)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 rootKey.length)
    (hx23_1 : s1.readReg64 .x23 = l3)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = l2)
    (hx26_1 : s1.readReg64 .x26 = p1)
    (hx28_1 : s1.readReg64 .x28 = c3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8812#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 128#64) ↦₆₄ v128) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ v144) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ v192) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₃₂ d200) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ v208) ∗
        vecU8Payload A.repAlloc c1 p1 rootKey ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ (p1_new : BitVec 64) (d184' : BitVec 32),
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 128#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            (((s0.sp - 2400#64) + 184#64) ↦₃₂ d184') ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗
            (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecCapPtrDealloc A.repAlloc c1 p1 ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents rootKey) st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
          sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = c0 ∧ sm.readReg64 .x21 = c2 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 rootKey.length ∧ sm.readReg64 .x23 = l3 ∧
          sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = l2 ∧ sm.readReg64 .x26 = p1 ∧
          sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0) :=
  v6hr_clone_rootKey_3796_to_8812_of_placedHooks hA.toPlacedBudget
    st s0 s1 out c0 p0 c1 p1 c2 p2 l2 ep c3 l3 w120 v128 v144 v192 v208
    d112 d116 d184 d200 rootKey Rest hfits hsp0_align hpc1 hrun1 hsp1
    hx8_1 hx9_1 hx11_1 hx12_1 hx13_1 hx14_1 hx19_1 hx20_1 hx21_1 hx22_1
    hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 htr1

/-- Clones `authPb.macKey` at `+8812 -> +9852` under
    `FitsEvents M lim st (authKeyCloneEvents macKey)` without panic or OOM:
    saves `c0` (`x20`) in `x27`, stores `l2` at `[fsp + 216]` and `p2_new` at `[fsp + 136]`,
    producing `vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey` and
    weakening the original buffer to `vecCapPtrDealloc A.repAlloc c2 p2`. -/
theorem v6hr_clone_macKey_8812_to_9852_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State)
    (out c0 c1 p1 l1 c2 p2 c3 l3 v136 v216 : BitVec 64)
    (d112 d116 : BitVec 32) (macKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents macKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 8812#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d112.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d116.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = c0)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = l3)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = BitVec.ofNat 64 macKey.length)
    (hx26_1 : s1.readReg64 .x26 = p1)
    (hx28_1 : s1.readReg64 .x28 = c3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9852#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ v136) ∗ (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗
        vecU8Payload A.repAlloc c2 p2 macKey ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ p2_new : BitVec 64,
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗
            (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            vecCapPtrDealloc A.repAlloc c2 p2 ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents macKey) st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
          sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = c2 ∧ sm.readReg64 .x22 = l1 ∧
          sm.readReg64 .x23 = l3 ∧ sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x26 = p1 ∧
          sm.readReg64 .x27 = c0 ∧ sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  generalize hfsp_eq : s0.sp - 2400#64 = fsp at hfsp_align hsp1 ⊢
  clear hfsp_eq hsp0_align
  have hm_cases : macKey = [] ∨ 0 < macKey.length := by cases macKey <;> simp
  rcases hm_cases with hm_nil | hm_pos
  · have hevs : authKeyCloneEvents macKey = [] := by simp [authKeyCloneEvents, hm_nil]
    rw [hevs, M.stepEvents_nil]
    rw [hm_nil] at hx25_1 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx25_1 ⊢
    refine SepWP.mono
      (post := fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 136#64) ↦₆₄ 1#64) ∗ ((fsp + 200#64) ↦₃₂ d116) ∗
          ((fsp + 208#64) ↦₆₄ p2) ∗ ((fsp + 216#64) ↦₆₄ 0#64) ∗
          vecU8Payload A.repAlloc 0#64 1#64 [] ∗
          vecCapPtrDealloc A.repAlloc c2 p2 ∗
          A.pool lim st sm ∗ Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = c2 ∧ sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = l3 ∧ sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x26 = p1 ∧
        sm.readReg64 .x27 = c0 ∧ sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0)
      ?_
      fun _ _ _ _ ⟨hPm, hregs⟩ => ⟨1#64, hPm, hregs⟩
    refine seq_clean_st
      (mid := lsmpl.base 333 + 9844#64)
      (P_mid := fun sm =>
        stackAt fsp encoderFromPbStack ∗
        ((fsp + 136#64) ↦₆₄ v136) ∗ ((fsp + 200#64) ↦₃₂ d116) ∗
        ((fsp + 208#64) ↦₆₄ p2) ∗ ((fsp + 216#64) ↦₆₄ 0#64) ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st sm ∗ Rest)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = c2 ∧ sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = l3 ∧ sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x26 = p1 ∧
        sm.readReg64 .x27 = c0 ∧ sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · change s1.pc = (blkPl_333).base + 8812#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 9844#64) s1 _ _
      wp_steps_sync_333 ((blkPl_333).base + 9844#64)
      simp only [State.setMem_setMem]
      have hd := vecU8Payload_entails_dealloc A.repAlloc c2 p2 []
      refine entails_pre_st ?_ ?_
      · intro sc hsc; rw [← hsc]
        refine Entails.trans (Entails.of_eq (show _ =
          vecU8Payload A.repAlloc c2 p2 [] ∗
          (stackAt fsp encoderFromPbStack ∗
           ((fsp + 136#64) ↦₆₄ v136) ∗ ((fsp + 200#64) ↦₃₂ d116) ∗
           ((fsp + 208#64) ↦₆₄ p2) ∗ ((fsp + 216#64) ↦₆₄ 0#64) ∗
           A.pool lim st sc ∗ Rest) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hd) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx11_2, hx12_2, hx19_2, hx21_2, hx22_2,
        hx23_2, hx24_2, hx26_2, hx27_2, hx28_2, htr2⟩
      change s2.pc = (blkPl_333).base + 9844#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 9852#64) s2 _ _
      wp_steps_sync_333 ((blkPl_333).base + 9852#64)
      simp only [State.setMem_setMem]
      have hn := vecU8Payload_of_nil A.repAlloc
      dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
      refine entails_pre_st ?_ ?_
      · intro sc hsc; rw [← hsc]
        refine Entails.trans (Entails.of_eq (show _ =
          emp ∗
          (stackAt fsp encoderFromPbStack ∗
           ((fsp + 136#64) ↦₆₄ 1#64) ∗ ((fsp + 200#64) ↦₃₂ d116) ∗
           ((fsp + 208#64) ↦₆₄ p2) ∗ ((fsp + 216#64) ↦₆₄ 0#64) ∗
           vecCapPtrDealloc A.repAlloc c2 p2 ∗
           A.pool lim st sc ∗ Rest) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hn) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
  · have hne_nil : macKey.isEmpty = false := by
      cases h : macKey with | nil => simp [h] at hm_pos | cons => rfl
    have hevs : authKeyCloneEvents macKey = rustAllocEvents macKey.length 1 := by
      simp [authKeyCloneEvents, hne_nil]
    rw [hevs] at hfits ⊢
    refine SepWP.weaken_pre (Entails.trans
      (Entails.of_eq (show _ =
        vecU8Payload A.repAlloc c2 p2 macKey ∗
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 136#64) ↦₆₄ v136) ∗ ((fsp + 200#64) ↦₃₂ d116) ∗
         ((fsp + 208#64) ↦₆₄ p2) ∗ ((fsp + 216#64) ↦₆₄ v216) ∗
         A.pool lim st s1 ∗ Rest) by sep_ac_rfl))
      (Entails.trans
        (sepConj_mono_left (vecU8Payload_pos_unpack A.repAlloc c2 p2 macKey hm_pos))
        (Entails.of_eq (show _ =
          ⌜macKey.length ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 ∧ p2 ≠ 0#64 ∧ c2 ≠ 0#64⌝ ∗
          (memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
           ((fsp + 136#64) ↦₆₄ v136) ∗ ((fsp + 200#64) ↦₃₂ d116) ∗
           ((fsp + 208#64) ↦₆₄ p2) ∗ ((fsp + 216#64) ↦₆₄ v216) ∗
           A.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
           memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length) ∗
           A.pool lim st s1 ∗ Rest) by
          rw [stackAt_encoderFromPb_split_allocHook fsp]
          dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
          sep_ac_rfl)))) ?_
    apply SepWP.pure_elim
    rintro ⟨hm_le, hm_cap, hp2_ne, hc2_ne⟩
    have hm_lt63 : macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
    have hm_lt64 : macKey.length < 2 ^ 64 := by omega
    have hm_toNat : (BitVec.ofNat 64 macKey.length).toNat = macKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
    have hm_ne0 : (BitVec.ofNat 64 macKey.length == 0#64) = false :=
      ofNat_beq_zero_false hm_pos hm_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hrlay : RustLayoutOk macKey.length 1 := ⟨⟨hm_pos, hpow1, hm_lt63⟩, by decide⟩
    have hshim := hA.shim_ok
    dsimp only [rustAllocShimVmSpec] at hshim
    have halloc := subroutine_ok_allocNoOom_of_budget hA.alloc_ok
    dsimp only [rustCliAllocNoOomSpec] at halloc
    have hmc := hA.memcpy_ok
    dsimp only [allocMemcpyVmSpec] at hmc
    clear hA
    change s1.pc = (blkPl_333).base + 8812#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9852#64) s1 _ _
    wp_steps_sync_333 (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp_shim : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_333 (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (macKey.length, 1, st)
    have hoom0 : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
    have hoom0_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_false_of_ne hoom0
    have hacp_alloc : AllocCallPreserved s1 sf_1 :=
      hacp_shim.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
    wp_steps_sync_333 (lsρ "memcpy")
    simp only [State.setMem_setMem]
    wp_call hmc (sf_1.readReg64 .x0, p2, macKey)
    have hacp_mc : AllocCallPreserved s1 sf_2 :=
      hacp_alloc.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_2›)
    have hsp_sf : sf.sp = fsp := by simp only [wp_norm, arm64_norm, *]
    have hsp_sf1 : sf_1.sp = fsp := by simp only [wp_norm, arm64_norm, *]
    have hsp_sf2 : sf_2.sp = fsp := by simp only [wp_norm, arm64_norm, *]
    have htr_sf2 : sf_2.trace = s0.trace := hacp_mc.2.1.trans htr1.1
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 := by
      simp only [wp_norm, arm64_norm, htr1.2, *]
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    refine SepWP.mono
      (post := fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 136#64) ↦₆₄ sf_1.readReg64 .x0) ∗ ((fsp + 200#64) ↦₃₂ d116) ∗
          ((fsp + 208#64) ↦₆₄ p2) ∗
          ((fsp + 216#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length)
            (sf_1.readReg64 .x0) macKey ∗
          vecCapPtrDealloc A.repAlloc c2 p2 ∗
          A.pool lim (M.stepEvents (rustAllocEvents macKey.length 1) st) sm ∗ Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = c2 ∧ sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = l3 ∧ sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x26 = p1 ∧
        sm.readReg64 .x27 = c0 ∧ sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0)
      ?_
      fun _ _ _ _ ⟨hPm, hregs⟩ => ⟨sf_1.readReg64 .x0, hPm, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 9852#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_pos_dealloc A.repAlloc c2 p2 macKey hm_le hm_cap hp2_ne hc2_ne
    have hp := vecU8Payload_pos A.repAlloc (sf_1.readReg64 .x0) macKey hm_pos hm_lt63 hoom0
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc, stackAt_encoderFromPb_split_allocHook fsp]
      simp only [hsp_sf, hsp_sf1, hsp_sf2]
      refine Entails.trans (Entails.of_eq (show _ =
        (A.repAlloc.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
         memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length)) ∗
        (A.repAlloc.live (sf_1.readReg64 .x0) macKey.length 1 ∗
         (sf_1.readReg64 .x0 ↦ₛ macKey)) ∗
        (memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
         ((fsp + 136#64) ↦₆₄ sf_1.readReg64 .x0) ∗ ((fsp + 200#64) ↦₃₂ d116) ∗
         ((fsp + 208#64) ↦₆₄ p2) ∗
         ((fsp + 216#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
         A.pool lim (M.stepEvents (rustAllocEvents macKey.length 1) st) sc ∗ Rest) by
        dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

theorem v6hr_clone_macKey_8812_to_9852_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State)
    (out c0 c1 p1 l1 c2 p2 c3 l3 v136 v216 : BitVec 64)
    (d112 d116 : BitVec 32) (macKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents macKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 8812#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d112.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d116.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = c0)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = l3)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = BitVec.ofNat 64 macKey.length)
    (hx26_1 : s1.readReg64 .x26 = p1)
    (hx28_1 : s1.readReg64 .x28 = c3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9852#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ v136) ∗ (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗
        vecU8Payload A.repAlloc c2 p2 macKey ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ p2_new : BitVec 64,
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 200#64) ↦₃₂ d116) ∗
            (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            vecCapPtrDealloc A.repAlloc c2 p2 ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents macKey) st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
          sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = c2 ∧ sm.readReg64 .x22 = l1 ∧
          sm.readReg64 .x23 = l3 ∧ sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x26 = p1 ∧
          sm.readReg64 .x27 = c0 ∧ sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0) :=
  v6hr_clone_macKey_8812_to_9852_of_placedHooks hA.toPlacedBudget
    st s0 s1 out c0 c1 p1 l1 c2 p2 c3 l3 v136 v216 d112 d116 macKey Rest
    hfits hsp0_align hpc1 hrun1 hsp1 hx11_1 hx12_1 hx19_1 hx20_1 hx21_1
    hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6cPlacedBudgetAux
