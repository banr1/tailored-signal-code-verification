/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGet
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Return-Tail Helpers for `<spqr::chain::Chain>::recv_key` (Block `366`)

Defines `RecvKeyPlacedStateInv`, `recvKeyPost`, `recvKeyPanic`, and the relocatable
`[LibsignalPlacement]` epilogue and `Ok`/`Err` return-tail lemmas for Block `366` under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open CryptoVerification (LibsignalPlacement lsmpl blkPC_366 blkPl_366)
open CryptoVerification.LibsignalSpqrV1 (Bytes Chain HkdfFn)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainRecvKeyGhost
  calleeSavedRecvKeyAt chainRepr memRegion_32_err_epoch_split memRegion_32_err_jump_split
  memRegion_32_err_u32_split memRegion_32_ok_split nextKeyInternalStackX
  recvKeyErrAt_epochOutOfRange_intro recvKeyErrAt_keyAlreadyRequested_intro
  recvKeyErrAt_keyJump_intro recvKeyErrAt_keyTrimmed_intro recvKeyFrameRestAt
  recvKeyOkAt_alloc_intro recvKeyPostAt rejoin_stack_chainRecvKeyX
)
open CryptoVerification.SpqrV1.ChainProofs.AgreeStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (LsCallInv)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget (
  chainRecvKeyEvents chainRecvKeySpecX
)

namespace LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetBudget

open Arm64 ProofLib
open ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre

/-- Normal-return postcondition of `SepWPp` for budget-threaded `<spqr::chain::Chain>::recv_key`. -/
abbrev recvKeyPost (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hkdf : HkdfFn) (x : ChainRecvKeyGhost) (st : M.σ) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    (P' ⊢ (chainRecvKeySpecX M A lim hkdf).post (x, st) s0 sf)

/-- Panic-outcome postcondition of `SepWPp` for budget-threaded `<spqr::chain::Chain>::recv_key`. -/
abbrev recvKeyPanic (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hkdf : HkdfFn) (x : ChainRecvKeyGhost) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P' => (sf.mem ⊨ P' ∗ R) → (sf.mem ⊨ (chainRecvKeySpecX M A lim hkdf).onPanic (x, st) s0 sf ∗ R)

/-- Relocatable state invariant across `<spqr::chain::Chain>::recv_key` (`sp = s0.sp - 128#64`)
including `AllocCallPreserved s0 s`. -/
structure RecvKeyPlacedStateInv (lsmpl : Obj.MultiPlacement) (s0 s : State) : Prop where
  hF : LsCallInv lsmpl s.mem
  hrun : s.status = .Running
  hsp : s.sp = s0.sp - 128#64
  hsp0_align : s0.spAligned = true
  hx26 : s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5)
  hx27 : s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)
  hx28 : s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5)
  htrace : s.trace = s0.trace
  hvregs : calleeSavedVRegs s = calleeSavedVRegs s0
  hacp : AllocCallPreserved s0 s

theorem RecvKeyPlacedStateInv.spAligned {lsmpl : Obj.MultiPlacement} {s0 s : State}
    (h : RecvKeyPlacedStateInv lsmpl s0 s) : s.spAligned = true := by
  have h0 := h.hsp0_align; have hsp := h.hsp
  simp only [State.spAligned, hsp] at h0 ⊢; revert h0; bv_kernel

theorem allowPanic_recvKey_panic {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {hkdf : HkdfFn}
    {x : ChainRecvKeyGhost} {st : M.σ} {s0 sf : State} {P R : SepProp}
    (hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true)
    (htr : sf.trace = s0.trace) (hm : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ (chainRecvKeySpecX M A lim hkdf).onPanic (x, st) s0 sf ∗ R := by
  dsimp only [chainRecvKeySpecX]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hpan, htr⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap P)) hm⟩

private theorem seq_sepWPp_lsCallInv_vm {P : Program} {b : BitVec 64}
    {H : String → Option (State → State)} {pl : Obj.MultiPlacement}
    {mid target_pc : BitVec 64} {s : State} {Pre P_mid : SepProp} {Q : State → Prop}
    {post post_err : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (h1 : SepWP (P.rebase b H) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, LsCallInv pl sm.mem → VmPreserved s sm →
      sm.pc = mid → sm.status = .Running → Q sm →
      SepWPp (P.rebase b H) target_pc sm P_mid post post_err) :
    SepWPp (P.rebase b H) target_pc s Pre post post_err :=
  CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts.SepWPp.of_sepWP_lsCallInv hF
    (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ hF' R hm hL =>
      h2 sm hF' hvm hpc hrun hQ R (Satisfies.mono (sepConj_mono_left hent) hm) hL)

theorem recvKey_epilogue_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hkdf : HkdfFn}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (st : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 248#64) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        recvKeyPostAt A.repAlloc x.selfPtr x.out x.self (Chain.recvKey hkdf x.self x.epoch x.index) ∗
        A.pool lim (M.stepEvents (chainRecvKeyEvents hkdf x) st) s)
      (recvKeyPost M A lim hkdf x st s0)
      (recvKeyPanic M A lim hkdf x st s0 R) := by
  intro prog
  dsimp only [prog] at *
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  unfold recvKeyFrameRestAt calleeSavedRecvKeyAt
  wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28
  wp_norm_hyp htrace; wp_norm_hyp hvregs
  apply SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.fold (rejoin_stack_chainRecvKeyX s0.sp
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x25) c3
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, ?_⟩
  dsimp only [chainRecvKeySpecX]
  simp only [LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
    LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64]
  refine Entails.pure_right ⟨by wp_norm_goal, by simp only [wp_norm, arm64_norm]; exact hacp⟩ ?_
  sep_frame

theorem recvKey_ok_from_708_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hkdf : HkdfFn}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (st : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (self' : Chain) (outKey : Bytes) (p_key : BitVec 64)
    (hp_key : p_key ≠ 0#64) (hlen_key : outKey.length = 32)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = .ok (self', outKey))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 708#64)
    (hx0 : s.readReg64 (.gpr 0#5) = p_key)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ A.live p_key 32 1 ∗ (p_key ↦ₛ outKey) ∗
        chainRepr A.repAlloc x.selfPtr self' ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool lim (M.stepEvents (chainRecvKeyEvents hkdf x) st) s)
      (recvKeyPost M A lim hkdf x st s0) (recvKeyPanic M A lim hkdf x st s0 R) := by
  intro prog
  have h_epi := @recvKey_epilogue_placed _ M A lim hkdf H x st s0 c3 R
  dsimp only [prog] at *
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  rw [memRegion_32_ok_split x.out, ← LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro v0; apply SepWPp.exists_elim; intro v8
  apply SepWPp.exists_elim; intro v16; apply SepWPp.exists_elim; intro v24
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hx0; wp_norm_hyp hx19
  refine seq_sepWPp_lsCallInv_vm (mid := (blkPl_366).base + 248#64)
    (P_mid :=
      stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        recvKeyPostAt A.repAlloc x.selfPtr x.out x.self (Chain.recvKey hkdf x.self x.epoch x.index) ∗
        A.pool lim (M.stepEvents (chainRecvKeyEvents hkdf x) st) s)
    (Q := fun sm =>
      sm.sp = s0.sp - 128#64 ∧
      sm.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
      sm.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
      sm.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
      sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
      AllocCallPreserved s0 sm)
    hF ?_ ?_
  · by_vm_steps
      wp_steps
      refine SepWP.fold (recvKeyOkAt_alloc_intro A.repAlloc x.out p_key outKey hp_key hlen_key)
        (by sep_focus) ?_
      rw [hres]; dsimp only [recvKeyPostAt]
      rw [← hx26, ← hx27, ← hx28, ← htrace, ← hvregs]
      wp_done
  · intro sm hF' hvm hpc' hrun' ⟨hsp', hx26', hx27', hx28', htrace', hvregs', hacp'⟩
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 sm :=
      ⟨hF', hrun', hsp', hsp0_align, hx26', hx27', hx28', htrace', hvregs', hacp'⟩
    rw [← A.pool_of_vmPreserved hvm]
    exact h_epi sm hinv' hpc'

theorem recvKey_err_keyTrimmed_from_884_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hkdf : HkdfFn}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (st : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.keyTrimmed x.index)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 884#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 8 = 10#8)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainRepr A.repAlloc x.selfPtr x.self ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool lim (M.stepEvents (chainRecvKeyEvents hkdf x) st) s)
      (recvKeyPost M A lim hkdf x st s0) (recvKeyPanic M A lim hkdf x st s0 R) := by
  intro prog
  have h_epi := @recvKey_epilogue_placed _ M A lim hkdf H x st s0 c3 R
  dsimp only [prog] at *
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  rw [memRegion_32_err_u32_split x.out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro v0; apply SepWPp.exists_elim; intro v8; apply SepWPp.exists_elim; intro v12
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hw8; wp_norm_hyp hx19; wp_norm_hyp hw20
  refine seq_sepWPp_lsCallInv_vm (mid := (blkPl_366).base + 248#64)
    (P_mid :=
      stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        recvKeyPostAt A.repAlloc x.selfPtr x.out x.self (Chain.recvKey hkdf x.self x.epoch x.index) ∗
        A.pool lim (M.stepEvents (chainRecvKeyEvents hkdf x) st) s)
    (Q := fun sm =>
      sm.sp = s0.sp - 128#64 ∧
      sm.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
      sm.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
      sm.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
      sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
      AllocCallPreserved s0 sm)
    hF ?_ ?_
  · by_vm_steps
      wp_steps
      refine SepWP.fold (recvKeyErrAt_keyTrimmed_intro x.out x.index) (by sep_focus) ?_
      rw [hres]; dsimp only [recvKeyPostAt]
      rw [← hx26, ← hx27, ← hx28, ← htrace, ← hvregs]
      wp_done
  · intro sm hF' hvm hpc' hrun' ⟨hsp', hx26', hx27', hx28', htrace', hvregs', hacp'⟩
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 sm :=
      ⟨hF', hrun', hsp', hsp0_align, hx26', hx27', hx28', htrace', hvregs', hacp'⟩
    rw [← A.pool_of_vmPreserved hvm]
    exact h_epi sm hinv' hpc'

theorem recvKey_err_keyAlreadyRequested_from_880_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hkdf : HkdfFn}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (st : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.keyAlreadyRequested x.index)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 880#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainRepr A.repAlloc x.selfPtr x.self ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool lim (M.stepEvents (chainRecvKeyEvents hkdf x) st) s)
      (recvKeyPost M A lim hkdf x st s0) (recvKeyPanic M A lim hkdf x st s0 R) := by
  intro prog
  have h_epi := @recvKey_epilogue_placed _ M A lim hkdf H x st s0 c3 R
  dsimp only [prog] at *
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  rw [memRegion_32_err_u32_split x.out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro v0; apply SepWPp.exists_elim; intro v8; apply SepWPp.exists_elim; intro v12
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hx19; wp_norm_hyp hw20
  refine seq_sepWPp_lsCallInv_vm (mid := (blkPl_366).base + 248#64)
    (P_mid :=
      stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        recvKeyPostAt A.repAlloc x.selfPtr x.out x.self (Chain.recvKey hkdf x.self x.epoch x.index) ∗
        A.pool lim (M.stepEvents (chainRecvKeyEvents hkdf x) st) s)
    (Q := fun sm =>
      sm.sp = s0.sp - 128#64 ∧
      sm.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
      sm.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
      sm.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
      sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
      AllocCallPreserved s0 sm)
    hF ?_ ?_
  · by_vm_steps
      wp_steps
      refine SepWP.fold (recvKeyErrAt_keyAlreadyRequested_intro x.out x.index) (by sep_focus) ?_
      rw [hres]; dsimp only [recvKeyPostAt]
      rw [← hx26, ← hx27, ← hx28, ← htrace, ← hvregs]
      wp_done
  · intro sm hF' hvm hpc' hrun' ⟨hsp', hx26', hx27', hx28', htrace', hvregs', hacp'⟩
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 sm :=
      ⟨hF', hrun', hsp', hsp0_align, hx26', hx27', hx28', htrace', hvregs', hacp'⟩
    rw [← A.pool_of_vmPreserved hvm]
    exact h_epi sm hinv' hpc'

theorem recvKey_err_keyJump_from_204_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hkdf : HkdfFn}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (st : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (ctr : BitVec 32)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.keyJump ctr x.index)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 204#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 32 = ctr)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainRepr A.repAlloc x.selfPtr x.self ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool lim (M.stepEvents (chainRecvKeyEvents hkdf x) st) s)
      (recvKeyPost M A lim hkdf x st s0) (recvKeyPanic M A lim hkdf x st s0 R) := by
  intro prog
  have h_epi := @recvKey_epilogue_placed _ M A lim hkdf H x st s0 c3 R
  dsimp only [prog] at *
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  rw [memRegion_32_err_jump_split x.out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro v0; apply SepWPp.exists_elim; intro v8
  apply SepWPp.exists_elim; intro v12; apply SepWPp.exists_elim; intro v16
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hw8; wp_norm_hyp hx19; wp_norm_hyp hw20
  refine seq_sepWPp_lsCallInv_vm (mid := (blkPl_366).base + 248#64)
    (P_mid :=
      stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        recvKeyPostAt A.repAlloc x.selfPtr x.out x.self (Chain.recvKey hkdf x.self x.epoch x.index) ∗
        A.pool lim (M.stepEvents (chainRecvKeyEvents hkdf x) st) s)
    (Q := fun sm =>
      sm.sp = s0.sp - 128#64 ∧
      sm.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
      sm.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
      sm.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
      sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
      AllocCallPreserved s0 sm)
    hF ?_ ?_
  · by_vm_steps
      wp_steps
      refine SepWP.fold (recvKeyErrAt_keyJump_intro x.out ctr x.index) (by sep_focus) ?_
      rw [hres]; dsimp only [recvKeyPostAt]
      rw [← hx26, ← hx27, ← hx28, ← htrace, ← hvregs]
      wp_done
  · intro sm hF' hvm hpc' hrun' ⟨hsp', hx26', hx27', hx28', htrace', hvregs', hacp'⟩
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 sm :=
      ⟨hF', hrun', hsp', hsp0_align, hx26', hx27', hx28', htrace', hvregs', hacp'⟩
    rw [← A.pool_of_vmPreserved hvm]
    exact h_epi sm hinv' hpc'

theorem recvKey_err_epochOutOfRange_from_228_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hkdf : HkdfFn}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (st : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.epochOutOfRange x.epoch)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 228#64)
    (hx2 : s.readReg64 (.gpr 2#5) = x.epoch)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainRepr A.repAlloc x.selfPtr x.self ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool lim (M.stepEvents (chainRecvKeyEvents hkdf x) st) s)
      (recvKeyPost M A lim hkdf x st s0) (recvKeyPanic M A lim hkdf x st s0 R) := by
  intro prog
  have h_epi := @recvKey_epilogue_placed _ M A lim hkdf H x st s0 c3 R
  dsimp only [prog] at *
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  rw [memRegion_32_err_epoch_split x.out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro v0; apply SepWPp.exists_elim; intro v8; apply SepWPp.exists_elim; intro v16
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hx2; wp_norm_hyp hx19
  refine seq_sepWPp_lsCallInv_vm (mid := (blkPl_366).base + 248#64)
    (P_mid :=
      stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        recvKeyPostAt A.repAlloc x.selfPtr x.out x.self (Chain.recvKey hkdf x.self x.epoch x.index) ∗
        A.pool lim (M.stepEvents (chainRecvKeyEvents hkdf x) st) s)
    (Q := fun sm =>
      sm.sp = s0.sp - 128#64 ∧
      sm.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
      sm.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
      sm.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
      sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
      AllocCallPreserved s0 sm)
    hF ?_ ?_
  · by_vm_steps
      wp_steps
      refine SepWP.fold (recvKeyErrAt_epochOutOfRange_intro x.out x.epoch) (by sep_focus) ?_
      rw [hres]; dsimp only [recvKeyPostAt]
      rw [← hx26, ← hx27, ← hx28, ← htrace, ← hvregs]
      wp_done
  · intro sm hF' hvm hpc' hrun' ⟨hsp', hx26', hx27', hx28', htrace', hvregs', hacp'⟩
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 sm :=
      ⟨hF', hrun', hsp', hsp0_align, hx26', hx27', hx28', htrace', hvregs', hacp'⟩
    rw [← A.pool_of_vmPreserved hvm]
    exact h_epi sm hinv' hpc'

end LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetBudget
