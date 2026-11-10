/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSym
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.ProtoExtBudget
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable `ErrTail` Symbolic Execution Lemmas

Symbolic execution step and loop lemmas for `ErrTail` on block `130`, threading
`RustCliAllocBudget M` and `VmPreserved` across SPE copying, `Chain` element drops, and buffer
deallocations.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSymBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ReceiverChain)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement lsmpl lsρ
  sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain ls_subroutine_ok_of_block withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack arrayAt)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  dropChainStack lsRustDeallocSym ls_hook_ok_rustDealloc
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup (
  blkPC_131 blkPl_131 blkLib_eq_131
  errTailPC_placed errDropChainLoopPC_placed retEpiloguePC_placed tryDecryptEntry_placed
  tryDecryptWPInv words5At
  arrayAt_nil arrayAt_cons
  bv_ofNat_succ_sub_one bv_ofNat_succ_succ_bne_one bv_ofNat_succ_beq_zero
  sp_sub_1504_add_0x38 sp_sub_1504_add_0xe8 sp_sub_1504_add_0xf0
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs PoolPreserved
  RustCliAllocBudget VmPreserved rustDeallocEvents rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropChainSpec)
open LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.ProtoExtBudget (drop_chain_placed_ok)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private abbrev freeOnlyPool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s

private theorem freeOnlyPool_intro {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ freeOnlyPool A lim st s :=
  Entails.sepExists_right [] (Entails.pure_right FreeOnlyEvs.nil (Entails.refl _))

private theorem freeOnlyPool_keep {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {s sm : State}
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]) :
    A.pool lim (M.stepEvents evs st) s ⊢ freeOnlyPool A lim st sm := by
  rw [← A.pool_of_vmPreserved hvm]
  exact Entails.sepExists_right evs (Entails.pure_right hevs (Entails.refl _))

private theorem freeOnlyPool_dealloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    (sz al : Nat) {s sm : State}
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]) :
    A.pool lim (M.stepEvents (rustDeallocEvents sz al) (M.stepEvents evs st)) s ⊢
      freeOnlyPool A lim st sm := by
  rw [← A.pool_of_vmPreserved hvm, ← M.stepEvents_append evs (rustDeallocEvents sz al) st]
  exact Entails.sepExists_right (evs ++ rustDeallocEvents sz al)
    (Entails.pure_right (FreeOnlyEvs.append hevs (FreeOnlyEvs.singleton al sz)) (Entails.refl _))

private theorem freeOnlyPool_append {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs1 evs2 : List AllocEvent}
    (hevs1 : FreeOnlyEvs evs1) (hevs2 : FreeOnlyEvs evs2) {s sm : State}
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]) :
    A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s ⊢
      freeOnlyPool A lim st sm := by
  rw [← A.pool_of_vmPreserved hvm, ← M.stepEvents_append evs1 evs2 st]
  exact Entails.sepExists_right (evs1 ++ evs2)
    (Entails.pure_right (FreeOnlyEvs.append hevs1 hevs2) (Entails.refl _))

private theorem freeOnlyPool_congr_vm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s sm : State} (hvm : VmPreserved s sm) :
    freeOnlyPool A lim st s = freeOnlyPool A lim st sm := by
  unfold freeOnlyPool
  simp only [A.pool_of_vmPreserved hvm]

private theorem SepWP.unpack_freeOnlyPool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {target : BitVec 64} {s : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s) ∗ Frame := by
      try dsimp only [freeOnlyPool]
      sep_focus)
    (hk : ∀ evs : List AllocEvent, FreeOnlyEvs evs →
      SepWP prog target s (A.pool lim (M.stepEvents evs st) s ∗ Frame) post) :
    SepWP prog target s P post := by
  rw [hf]
  wp_pull_exists
  rename_i evs
  exact SepWP.pure_elim (hk evs)

private theorem SepWP.sync_pool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim st s ∗ Frame := by sep_focus)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (A.pool lim st sm ∗ Frame) post) :
    SepWP prog target sm P post := by
  rw [hf, ← A.pool_of_vmPreserved hvm]
  exact hk

/-! ## Multi-Placed (`[LibsignalPlacement]`) Budget-Threaded `ErrTail` Step Lemmas -/

/-- Budget-pool-transporting `ErrTail` SPE copy step (`+780 .. +820` of Block `130`). -/
theorem errTail_copy_spe_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    {ret tag chainsPtr chainsLen : BitVec 64}
    {w0 w1 w2 w3 w4 r0 r1 r2 r3 r4 r5 t0 t1 t2 : BitVec 64}
    {s0 s : State}
    (hpc : s.pc = errTailPC_placed)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx26 : s.readReg64 .x26 = tag) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog ((blkPl_131).base + 820#64) s
      (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ chainsLen) ∗
       ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗ ((sp + 0x150#64) ↦₆₄ t2) ∗
       words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5 ∗ A.pool lim ast s)
      (fun sf P =>
        P = (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ chainsLen) ∗
             ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
             words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗ A.pool lim ast sf) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x20 = chainsPtr ∧ sf.readReg64 .x21 = chainsLen) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [errTailPC_placed, tryDecryptEntry_placed] at hpc
  unfold words5At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps_sync_pool ((blkPl_131).base + 820#64)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by sep_ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Drop one `Chain` element in `ErrTail`'s receiver-chains loop (`+828 .. +836` of Block `130`). -/
theorem errTail_drop_one_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    {p chainsPtr rem : BitVec 64} (gc : ChainGhost × ReceiverChain) {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = errDropChainLoopPC_placed)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = p)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog ((blkPl_131).base + 836#64) s
      (chainAt A.repAlloc gc p ∗ A.pool lim ast s ∗ stackAt sp dropChainStack)
      (fun sf P =>
        P = (memRegion p 104 ∗
             (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
             stackAt sp dropChainStack) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = p ∧ sf.readReg64 .x20 = chainsPtr ∧ sf.readReg64 .x21 = rem) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hdrop := ls_subroutine_ok_of_block (callerProg := (blkPC_131).rebase (blkPl_131).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (drop_chain_placed_ok hdealloc))
  rw [show CryptoVerification.LibsignalTripleRatchet.Getters.blkPl_142.base = lsmpl.base 142 from rfl] at hdrop
  simp only [withLsCodeLoaded, dropChainSpec] at hdrop
  dsimp only [errDropChainLoopPC_placed, tryDecryptEntry_placed] at hpc
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 142)
  wp_steps
  refine SepWP.sync_pool (hk := ?_)
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_call
  rw [← hsp]
  wp_call hdrop (⟨p, gc⟩, ast)
  refine SepWP.focus_weaken (freeOnlyPool_keep A lim ast ‹FreeOnlyEvs _› (VmPreserved.refl sf))
    (by sep_focus) ?_
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  rw [hsp]; unfold freeOnlyPool; sep_ac_rfl

/-- Loop-exit branch at `+836` (`rem = 1`), preserving `VmPreserved s sf`. -/
theorem errTail_drop_exit_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {chainsPtr : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 836#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = 1#64) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 848#64) s emp
      (fun sf P => P = emp ∧ tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr ∧
        VmPreserved s sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]⟩

/-- Loop-continue branch at `+836` (`rem ≠ 1`), preserving `VmPreserved s sf`. -/
theorem errTail_drop_cont_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {p chainsPtr rem : BitVec 64} {s0 s : State}
    (hne : (rem != 1#64) = true)
    (hpc : s.pc = (blkPl_131).base + 836#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = p)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) errDropChainLoopPC_placed s emp
      (fun sf P =>
        P = emp ∧ tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = p + 104#64 ∧ sf.readReg64 .x20 = chainsPtr ∧
        sf.readReg64 .x21 = rem - 1#64 ∧ VmPreserved s sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [errDropChainLoopPC_placed, tryDecryptEntry_placed]
  wp_steps
  try rw [hne, if_pos rfl]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]⟩

/-- Receiver-chains drop loop (`+828 .. +848` of Block `130`), threading `RustCliAllocBudget`. -/
theorem errTail_drop_loop_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    {chainsPtr : BitVec 64} {s0 : State}
    (rest : List (ChainGhost × ReceiverChain)) :
    ∀ {ast : M.σ} (gc : ChainGhost × ReceiverChain) (p : BitVec 64) (s : State),
      (rest.length + 1) * 104 < 2 ^ 63 →
      s.pc = errDropChainLoopPC_placed →
      tryDecryptWPInv s0 s →
      LibsignalCodeLoaded lsmpl s.mem →
      s.readReg64 .x19 = p →
      s.readReg64 .x20 = chainsPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 (rest.length + 1) →
      SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 848#64) s
        (arrayAt (chainAt A.repAlloc) 104 p (gc :: rest) ∗ A.pool lim ast s ∗
         stackAt (s0.sp - 1504#64) dropChainStack)
        (fun sf P =>
          P = (memRegion p ((rest.length + 1) * 104) ∗
               (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
               stackAt (s0.sp - 1504#64) dropChainStack) ∧
          tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr) := by
  induction rest with
  | nil =>
    intro ast gc p s hlt hpc hmeta hcl hx19 hx20 hx21
    rw [List.length_nil, Nat.zero_add] at hx21
    have hone := errTail_drop_one_wp_placed (ast := ast) (H := H) gc hdealloc hcl hpc hmeta hx19 hx20 hx21
    refine CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.SepWP.bind_framed
      (F := emp) hone ?_ ?_
    · rw [arrayAt_cons, arrayAt_nil, sepConj_emp, sepConj_emp]
    intro s1 P1 ⟨hP1, hmeta1, _, hx20_1, hx21_1⟩ hpc1
    subst hP1
    have hexit := errTail_drop_exit_wp_placed (H := H) hpc1 hmeta1 hx20_1 hx21_1
    refine CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.SepWP.bind_framed
      (F := memRegion p 104 ∗ freeOnlyPool A lim ast s1 ∗ stackAt (s0.sp - 1504#64) dropChainStack)
      hexit ?_ ?_
    · rw [emp_sepConj, sepConj_emp]
    intro sf Pf ⟨hPf, hmeta_f, hx20_f, hvm_f⟩ hpcf
    subst hPf
    rw [freeOnlyPool_congr_vm A lim ast hvm_f]
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f, hx20_f⟩
    rw [emp_sepConj, List.length_nil, Nat.zero_add, Nat.one_mul]
  | cons gc' rest' ih =>
    intro ast gc p s hlt hpc hmeta hcl hx19 hx20 hx21
    rw [List.length_cons] at hlt hx21
    have hone := errTail_drop_one_wp_placed (ast := ast) (H := H) gc hdealloc hcl hpc hmeta hx19 hx20 hx21
    refine CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.SepWP.bind_framed_lscl
      (F := arrayAt (chainAt A.repAlloc) 104 (p + 104#64) (gc' :: rest')) hcl hone ?_ ?_
    · rw [arrayAt_cons]; sep_ac_rfl
    intro s1 P1 ⟨hP1, hmeta1, hx19_1, hx20_1, hx21_1⟩ hpc1 hcl1
    subst hP1
    have hstep := errTail_drop_cont_wp_placed (H := H)
      (bv_ofNat_succ_succ_bne_one hlt) hpc1 hmeta1 hx19_1 hx20_1 hx21_1
    refine CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.SepWP.bind_framed_lscl
      (F := (memRegion p 104 ∗ freeOnlyPool A lim ast s1 ∗ stackAt (s0.sp - 1504#64) dropChainStack) ∗
            arrayAt (chainAt A.repAlloc) 104 (p + 104#64) (gc' :: rest')) hcl1 hstep ?_ ?_
    · rw [emp_sepConj]
    intro s2 P2 ⟨hP2, hmeta2, hx19_2, hx20_2, hx21_2, hvm2⟩ hpc2 hcl2
    subst hP2
    rw [freeOnlyPool_congr_vm A lim ast hvm2]
    refine SepWP.unpack_freeOnlyPool (hk := fun evs1 hevs1 => ?_)
    have hx21_2' : s2.readReg64 .x21 = BitVec.ofNat 64 (rest'.length + 1) := by
      rw [hx21_2, bv_ofNat_succ_sub_one (rest'.length + 1)]
    have hlt' : (rest'.length + 1) * 104 < 2 ^ 63 :=
      Nat.lt_trans (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (by decide)) hlt
    have hih := ih (ast := M.stepEvents evs1 ast) gc' (p + 104#64) s2
      hlt' hpc2 hmeta2 hcl2 hx19_2 hx20_2 hx21_2'
    refine CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.SepWP.bind_framed
      (F := memRegion p 104) hih ?_ ?_
    · sep_ac_rfl
    intro sf Pf ⟨hPf, hmeta_f, hx20_f⟩ hpcf
    subst hPf
    refine SepWP.unpack_freeOnlyPool (hk := fun evs2 hevs2 => ?_)
    refine SepWP.focus_weaken (freeOnlyPool_append A lim ast hevs1 hevs2 (VmPreserved.refl sf))
      (by sep_focus) ?_
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f, hx20_f⟩
    have hcomb : memRegion p ((rest'.length + 1 + 1) * 104) =
        memRegion p 104 ∗ memRegion (p + 104#64) ((rest'.length + 1) * 104) := by
      rw [show (rest'.length + 1 + 1) * 104 = 104 + (rest'.length + 1) * 104 by omega]
      exact ProofLib.memRegion_split p 104 ((rest'.length + 1) * 104) (by omega)
    rw [List.length_cons, hcomb]; unfold freeOnlyPool; sep_ac_rfl

/-- Empty receiver-chains branch at `+820` (`chainsLen = 0`), preserving `VmPreserved s sf`. -/
theorem errTail_drop_nil_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {chainsPtr : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 820#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = 0#64) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 848#64) s emp
      (fun sf P => P = emp ∧ tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr ∧
        VmPreserved s sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]⟩

/-- Non-empty receiver-chains loop entry at `+820` (`chainsLen ≠ 0`), preserving `VmPreserved s s1`. -/
theorem errTail_drop_init_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {chainsPtr rem : BitVec 64} {s0 s : State}
    (hne : (rem == 0#64) = false)
    (hpc : s.pc = (blkPl_131).base + 820#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) errDropChainLoopPC_placed s emp
      (fun s1 P1 =>
        P1 = emp ∧ tryDecryptWPInv s0 s1 ∧
        s1.readReg64 .x19 = chainsPtr ∧ s1.readReg64 .x20 = chainsPtr ∧ s1.readReg64 .x21 = rem ∧
        VmPreserved s s1) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [errDropChainLoopPC_placed, tryDecryptEntry_placed]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]⟩

/-- Drop all `receiver_chains` elements (`+820 .. +848` of Block `130`), threading `RustCliAllocBudget`. -/
theorem errTail_drop_chains_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    {chainsPtr : BitVec 64} {cs : List (ChainGhost × ReceiverChain)} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hlt : cs.length * 104 < 2 ^ 63)
    (hpc : s.pc = (blkPl_131).base + 820#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 cs.length) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 848#64) s
      (arrayAt (chainAt A.repAlloc) 104 chainsPtr cs ∗ A.pool lim ast s ∗
       stackAt (s0.sp - 1504#64) dropChainStack)
      (fun sf P =>
        P = (memRegion chainsPtr (cs.length * 104) ∗
             (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
             stackAt (s0.sp - 1504#64) dropChainStack) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr) := by
  cases cs with
  | nil =>
    rw [List.length_nil] at hx21
    have hstep := errTail_drop_nil_wp_placed (H := H) hpc hmeta hx20 hx21
    refine CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.SepWP.bind_framed
      (F := A.pool lim ast s ∗ stackAt (s0.sp - 1504#64) dropChainStack) hstep ?_ ?_
    · rw [arrayAt_nil]
    intro sf Pf ⟨hPf, hmeta_f, hx20_f, hvm_f⟩ hpcf
    subst hPf
    rw [← A.pool_of_vmPreserved hvm_f]
    refine SepWP.focus_weaken (freeOnlyPool_intro A lim ast sf) (by sep_focus) ?_
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f, hx20_f⟩
    rw [List.length_nil, Nat.zero_mul, memRegion_zero]; unfold freeOnlyPool; sep_ac_rfl
  | cons gc rest =>
    rw [List.length_cons] at hlt hx21 ⊢
    have hstep := errTail_drop_init_wp_placed (H := H) (bv_ofNat_succ_beq_zero hlt) hpc hmeta hx20 hx21
    refine CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.SepWP.bind_framed_lscl
      (F := arrayAt (chainAt A.repAlloc) 104 chainsPtr (gc :: rest) ∗ A.pool lim ast s ∗
            stackAt (s0.sp - 1504#64) dropChainStack) hcl hstep ?_ ?_
    · rw [emp_sepConj]
    intro s1 P1 ⟨hP1, hmeta1, hx19_1, hx20_1, hx21_1, hvm1⟩ hpc1 hcl1
    subst hP1
    rw [emp_sepConj, ← A.pool_of_vmPreserved hvm1]
    exact errTail_drop_loop_wp_placed (A := A) (lim := lim) (H := H)
      (chainsPtr := chainsPtr) (s0 := s0)
      hdealloc rest (ast := ast) gc chainsPtr s1 hlt hpc1 hmeta1 hcl1 hx19_1 hx20_1 hx21_1

/-- Deallocate the `receiver_chains` buffer (`+848 .. +876` of Block `130`), starting from `A.pool lim ast s`. -/
theorem errTail_dealloc_chains_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    {chainsCap chainsPtr : BitVec 64} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hlt : chainsCap.toNat * 104 < 2 ^ 63)
    (hpc : s.pc = (blkPl_131).base + 848#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 876#64) s
      (((s0.sp - 1504#64 + 0x38#64) ↦₆₄ chainsCap) ∗
       (if chainsCap = 0#64 then emp
        else A.repAlloc.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          memRegion chainsPtr (chainsCap.toNat * 104)) ∗
       A.pool lim ast s ∗ stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 0x38#64) ↦₆₄ chainsCap) ∗
             (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
             stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hdealloc_ok := ls_hook_ok_rustDealloc (prog := (blkPC_131).rebase (blkPl_131).base H) hdealloc
  simp only [rustCliDeallocBudgetSpec] at hdealloc_ok
  by_cases hcap : chainsCap = 0#64
  · subst hcap
    refine CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.SepWP.rw_pre
      (by simp only [ite_true, emp_sepConj, ← hsp]; exact rfl) ?_
    wp_steps
    refine SepWP.sync_pool (hk := ?_)
    refine SepWP.focus_weaken (freeOnlyPool_intro A lim ast _) (by sep_focus) ?_
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp]; unfold freeOnlyPool; sep_ac_rfl
  · refine CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.SepWP.rw_pre
      (by simp only [hcap, ite_false, ← hsp, RustCliAllocBudget.repAlloc_live]; exact rfl) ?_
    have hcap_beq : (chainsCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hmul : (chainsCap * 104#64).toNat = chainsCap.toNat * 104 := by
      rw [BitVec.toNat_mul, show (104#64 : BitVec 64).toNat = 104 from rfl,
          Nat.mod_eq_of_lt (by omega)]
    have hmul_bv : chainsCap * 104#64 = BitVec.ofNat 64 (chainsCap.toNat * 104) := by bv_omega
    wp_steps
    refine SepWP.sync_pool (hk := ?_)
    wp_call hdealloc_ok (chainsPtr, chainsCap.toNat * 104, 8, ast)
    refine SepWP.focus_weaken
      (freeOnlyPool_keep A lim ast (FreeOnlyEvs.singleton 8 (chainsCap.toNat * 104)) (VmPreserved.refl sf))
      (by sep_focus) ?_
    refine SepWP.done (by simp_all [AllocCallPreserved, arm64_norm])
      (by simp_all [AllocCallPreserved, arm64_norm]) ?_
    refine ⟨?_, ⟨by simp_all [AllocCallPreserved, arm64_norm],
      by simp_all [AllocCallPreserved, arm64_norm], hs0_align,
      by simp_all [AllocCallPreserved, arm64_norm],
      by simp_all [AllocCallPreserved, arm64_norm],
      by simp_all [AllocCallPreserved, arm64_norm]⟩⟩
    rw [hsp, sp_sub_1504_add_0x38]; unfold freeOnlyPool; sep_ac_rfl

/-- `freeOnlyPool`-input variant of `errTail_dealloc_chains_wp_placed` for chaining directly after
`errTail_drop_chains_wp_placed`. -/
theorem errTail_dealloc_chains_freeOnly_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    {chainsCap chainsPtr : BitVec 64} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hlt : chainsCap.toNat * 104 < 2 ^ 63)
    (hpc : s.pc = (blkPl_131).base + 848#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 876#64) s
      (((s0.sp - 1504#64 + 0x38#64) ↦₆₄ chainsCap) ∗
       (if chainsCap = 0#64 then emp
        else A.repAlloc.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          memRegion chainsPtr (chainsCap.toNat * 104)) ∗
       (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) s) ∗
       stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 0x38#64) ↦₆₄ chainsCap) ∗
             (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
             stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) := by
  refine SepWP.unpack_freeOnlyPool (hk := fun evs1 hevs1 => ?_)
  have h1 := errTail_dealloc_chains_wp_placed (ast := M.stepEvents evs1 ast) (H := H)
    hdealloc hlt hpc hmeta hx20
  refine CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.SepWP.bind_framed
    (F := emp) h1 (by sep_ac_rfl) ?_
  intro sf Pf ⟨hPf, hmeta_f⟩ hpcf
  subst hPf
  refine SepWP.unpack_freeOnlyPool (hk := fun evs2 hevs2 => ?_)
  refine SepWP.focus_weaken (freeOnlyPool_append A lim ast hevs1 hevs2 (VmPreserved.refl sf))
    (by sep_focus) ?_
  refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f⟩
  unfold freeOnlyPool; sep_ac_rfl

/-- Deallocate the `pq` buffer (`+876 .. retEpiloguePC_placed` of Block `130`), starting from `A.pool lim ast s`. -/
theorem errTail_dealloc_pq_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    {pqCap pqPtr : BitVec 64} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hpc : s.pc = (blkPl_131).base + 876#64)
    (hmeta : tryDecryptWPInv s0 s) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) retEpiloguePC_placed s
      (((s0.sp - 1504#64 + 0xe8#64) ↦₆₄ pqCap) ∗
       ((s0.sp - 1504#64 + 0xf0#64) ↦₆₄ pqPtr) ∗
       (if pqCap = 0#64 then emp
        else A.repAlloc.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat) ∗
       A.pool lim ast s ∗ stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 0xe8#64) ↦₆₄ pqCap) ∗
             ((s0.sp - 1504#64 + 0xf0#64) ↦₆₄ pqPtr) ∗
             (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
             stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hdealloc_ok := ls_hook_ok_rustDealloc (prog := (blkPC_131).rebase (blkPl_131).base H) hdealloc
  simp only [rustCliDeallocBudgetSpec] at hdealloc_ok
  dsimp only [retEpiloguePC_placed, tryDecryptEntry_placed]
  by_cases hcap : pqCap = 0#64
  · subst hcap
    refine CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.SepWP.rw_pre
      (by simp only [ite_true, emp_sepConj, ← hsp]; exact rfl) ?_
    wp_steps
    refine SepWP.sync_pool (hk := ?_)
    refine SepWP.focus_weaken (freeOnlyPool_intro A lim ast _) (by sep_focus) ?_
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp]; unfold freeOnlyPool; sep_ac_rfl
  · refine CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.SepWP.rw_pre
      (by simp only [hcap, ite_false, ← hsp, RustCliAllocBudget.repAlloc_live]; exact rfl) ?_
    have hcap_beq : (pqCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    wp_steps
    refine SepWP.sync_pool (hk := ?_)
    wp_call hdealloc_ok (pqPtr, pqCap.toNat, 1, ast)
    wp_steps
    refine SepWP.sync_pool (s := sf) (hk := ?_)
    refine SepWP.focus_weaken
      (freeOnlyPool_keep A lim ast (FreeOnlyEvs.singleton 1 pqCap.toNat) (VmPreserved.refl _))
      (by sep_focus) ?_
    refine SepWP.done (by simp_all [AllocCallPreserved, arm64_norm])
      (by simp_all [AllocCallPreserved, arm64_norm]) ?_
    refine ⟨?_, ⟨by simp_all [AllocCallPreserved, arm64_norm],
      by simp_all [AllocCallPreserved, arm64_norm], hs0_align,
      by simp_all [AllocCallPreserved, arm64_norm],
      by simp_all [AllocCallPreserved, arm64_norm],
      by simp_all [AllocCallPreserved, arm64_norm]⟩⟩
    rw [hsp, sp_sub_1504_add_0xe8, sp_sub_1504_add_0xf0]; unfold freeOnlyPool; sep_ac_rfl

/-- `freeOnlyPool`-input variant of `errTail_dealloc_pq_wp_placed` for chaining directly after
`errTail_dealloc_chains_freeOnly_wp_placed`. -/
theorem errTail_dealloc_pq_freeOnly_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    {pqCap pqPtr : BitVec 64} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hpc : s.pc = (blkPl_131).base + 876#64)
    (hmeta : tryDecryptWPInv s0 s) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) retEpiloguePC_placed s
      (((s0.sp - 1504#64 + 0xe8#64) ↦₆₄ pqCap) ∗
       ((s0.sp - 1504#64 + 0xf0#64) ↦₆₄ pqPtr) ∗
       (if pqCap = 0#64 then emp
        else A.repAlloc.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat) ∗
       (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) s) ∗
       stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 0xe8#64) ↦₆₄ pqCap) ∗
             ((s0.sp - 1504#64 + 0xf0#64) ↦₆₄ pqPtr) ∗
             (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
             stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) := by
  refine SepWP.unpack_freeOnlyPool (hk := fun evs1 hevs1 => ?_)
  have h1 := errTail_dealloc_pq_wp_placed (ast := M.stepEvents evs1 ast) (H := H)
    (pqCap := pqCap) (pqPtr := pqPtr) hdealloc hpc hmeta
  refine CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.SepWP.bind_framed
    (F := emp) h1 (by sep_ac_rfl) ?_
  intro sf Pf ⟨hPf, hmeta_f⟩ hpcf
  subst hPf
  refine SepWP.unpack_freeOnlyPool (hk := fun evs2 hevs2 => ?_)
  refine SepWP.focus_weaken (freeOnlyPool_append A lim ast hevs1 hevs2 (VmPreserved.refl sf))
    (by sep_focus) ?_
  refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f⟩
  unfold freeOnlyPool; sep_ac_rfl

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSymBudget
