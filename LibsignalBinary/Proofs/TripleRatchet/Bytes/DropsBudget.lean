/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import ProofLib.SepLogic.Basic
import ProofLib.SepLogic.WP
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded `bytes::Bytes` Drop Functions and Vtable Dispatch

Verifies relocatable `[LibsignalPlacement]` `VmPreserved` and `RustCliAllocBudget M` contracts for
`bytes::bytes::static_drop` (Block `224`), `promotable_even_drop` (Block `237`),
`promotable_odd_drop` (Block `236`), and unified vtable `drop` dispatch.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Bytes.DropsBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl lsρ
  ls_subroutine_ok_of_block withLsCodeLoaded subroutine_ok_withLsCodeLoaded_of_plain
  extract_withLsCodeLoaded
  blkPC_224 blkPl_224 blkLib_eq_224
  blkPC_236 blkPl_236 blkLib_eq_236
  blkPC_237 blkPl_237 blkLib_eq_237
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (
  BytesDropGhost extHookStack
  bytesPtr bytesData bytesBoxU8Buf bytesPlacedDropFnAddr
  lsBytesRustDeallocSym ls_hook_ok_rustDealloc getLsbD_zero_iff
)
open LibsignalBinary.Heap (
  VmPreserved AllocCostModel BudgetLimits RustCliAllocBudget
  rustDeallocEvents rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliDeallocBudgetSpecWithStack subroutine_ok_rustCliDeallocBudget_withStack
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget (
  bytesDropEvents bytesStaticDropSpec
  promotableEvenDropSpec promotableOddDropSpec bytesVtableDropSpec
  promotableEvenDropSpecX promotableOddDropSpecX bytesVtableDropSpecX
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Stack-Splitting, Arithmetic, and Tail-Call `__rust_dealloc` Helpers -/

private theorem stackAt_add_48_opt {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp hookStack 6 hstack

private theorem stackAt_add_48_comm_opt {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - BitVec.ofNat 64 hookStack) 48 ∗ stackAt sp hookStack := by
  unfold stackAt
  have h0 : hookStack + 48 = 48 + hookStack := Nat.add_comm hookStack 48
  have hsplit := memRegion_split (sp - BitVec.ofNat 64 (48 + hookStack)) 48 hookStack (by omega)
  have h1 : sp - BitVec.ofNat 64 (48 + hookStack) =
      sp - BitVec.ofNat 64 hookStack - 48#64 := by
    rw [BitVec.ofNat_add]
    bv_lin
  have h2 : sp - BitVec.ofNat 64 (48 + hookStack) + 48#64 =
      sp - BitVec.ofNat 64 hookStack := by
    rw [BitVec.ofNat_add]
    bv_lin
  rw [h0, hsplit, h2, h1]

private theorem pointsTo64_entails_exists (a v : BitVec 64) {R Q : SepProp}
    (h : R ⊢ Q) : ((a ↦₆₄ v) ∗ R) ⊢ ∃∗ x, (a ↦₆₄ x) ∗ Q :=
  Entails.trans (sepConj_mono_right h) (Entails.sepExists_intro (P := fun x => (a ↦₆₄ x) ∗ Q) v)

private theorem pointsTo64_entails_exists_single (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ ∃∗ x, (a ↦₆₄ x) :=
  Entails.sepExists_intro (P := fun x => a ↦₆₄ x) v

private theorem pointsTo64_6_entails_cells (base : BitVec 64)
    (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗
      ((base + 16#64) ↦₆₄ v2) ∗ ((base + 24#64) ↦₆₄ v3) ∗
      ((base + 32#64) ↦₆₄ v4) ∗ ((base + 40#64) ↦₆₄ v5)) ⊢ cells base 6 := by
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  exact pointsTo64_entails_exists _ v0
    (pointsTo64_entails_exists _ v1
      (pointsTo64_entails_exists _ v2
        (pointsTo64_entails_exists _ v3
          (pointsTo64_entails_exists _ v4
            (pointsTo64_entails_exists_single _ v5)))))

@[local simp, local arm64_norm]
private theorem getLsbD_or_one (ptr : BitVec 64) : (ptr ||| 1#64).getLsbD 0 = true := by
  bv_bits

private theorem or_one_and_not_one {ptr : BitVec 64} (h : (ptr &&& 1#64) = 0#64) :
    (ptr ||| 1#64) &&& (-2#64) = ptr := by
  bv_bits

private theorem odd_drop_add {off len : Nat} (hoff : off ≤ len) :
    BitVec.ofNat 64 off + BitVec.ofNat 64 (len - off) = BitVec.ofNat 64 len := by
  rw [← BitVec.ofNat_add, Nat.add_sub_of_le hoff]

private theorem ult_ofNat_false {off len : Nat} (hoff : off ≤ len) (hlen : len < 2 ^ 63) :
    (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 off) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : off < 2 ^ 64)]
  omega

private abbrev DeallocBudgetTailGhost (σ : Type) :=
  BitVec 64 × List (BitVec 8) × Nat × σ ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def rustDeallocBudgetTailSpecWithStack [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (hookStack : Nat) :
    Spec (DeallocBudgetTailGhost M.σ) where
  pre := fun (p, bs, align, st, v0, v1, v2, v3, v4, v5) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      (s.readReg64 .x2).toNat = align ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p bs.length align ∗ (p ↦ₛ bs) ∗
      stackAt (s.sp - 48#64) hookStack ∗
      ((s.sp - 48#64) ↦₆₄ v0) ∗ ((s.sp - 40#64) ↦₆₄ v1) ∗
      ((s.sp - 32#64) ↦₆₄ v2) ∗ ((s.sp - 24#64) ↦₆₄ v3) ∗
      ((s.sp - 16#64) ↦₆₄ v4) ∗ ((s.sp - 8#64) ↦₆₄ v5)
  post := fun (_, bs, align, st, _, _, _, _, _, _) s0 sf =>
    let st' := M.stepEvents (rustDeallocEvents bs.length align) st
    ⌜sf.trace = s0.trace ∧ M.liveBytes st' ≤ M.liveBytes st⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp (hookStack + 48)

private theorem deallocBudget_tail_ok_of_dealloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64)
    (hdealloc : subroutine_ok P addr (rustCliDeallocBudgetSpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (rustDeallocBudgetTailSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, bs, align, st, v0, v1, v2, v3, v4, v5⟩ R s0 hpc hrun hpre hsp
  have hcells :
      (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
        ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
        ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ⊢ cells (s0.sp - 48#64) 6 := by
    have h := pointsTo64_6_entails_cells (s0.sp - 48#64) v0 v1 v2 v3 v4 v5
    have ha1 : s0.sp - 48#64 + 8#64 = s0.sp - 40#64 := by bv_lin
    have ha2 : s0.sp - 48#64 + 16#64 = s0.sp - 32#64 := by bv_lin
    have ha3 : s0.sp - 48#64 + 24#64 = s0.sp - 24#64 := by bv_lin
    have ha4 : s0.sp - 48#64 + 32#64 = s0.sp - 16#64 := by bv_lin
    have ha5 : s0.sp - 48#64 + 40#64 = s0.sp - 8#64 := by bv_lin
    rwa [ha1, ha2, ha3, ha4, ha5] at h
  have hbs_mem := pointsToBytes_entails_memRegion p bs
  have hpre' : s0.mem ⊨
      (rustCliDeallocBudgetSpecWithStack M A lim hookStack).pre
        (p, bs.length, align, st) s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R) := by
    unfold rustDeallocBudgetTailSpecWithStack at hpre
    unfold rustCliDeallocBudgetSpecWithStack
    dsimp only at hpre ⊢
    have h1 : s0.mem ⊨
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
            (s0.readReg64 .x2).toNat = align ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
          A.pool lim st s0 ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
          (stackAt (s0.sp - 48#64) hookStack ∗ cells (s0.sp - 48#64) 6)) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hpre
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hbs_mem (sepConj_mono_right hcells))))
    rw [← stackAt_add_48_opt hstack, stackAt_add_48_comm_opt hstack] at h1
    have heq :
        ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
            (s0.readReg64 .x2).toNat = align ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
          A.pool lim st s0 ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
          (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ stackAt s0.sp hookStack)) ∗ R) =
        ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
            (s0.readReg64 .x2).toNat = align ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
          A.pool lim st s0 ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
          stackAt s0.sp hookStack) ∗
          (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R)) := by
      sep_ac_rfl
    exact heq ▸ h1
  refine hdealloc.mono_outcome (p, bs.length, align, st)
    (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    unfold rustDeallocBudgetTailSpecWithStack
    unfold rustCliDeallocBudgetSpecWithStack at hpost
    dsimp only at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hacp, hlive⟩, hmem_post⟩
    refine ⟨⟨hacp.2.1, hlive⟩, ?_⟩
    rw [stackAt_add_48_comm_opt hstack]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem_post
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-! ## 2. Stack-Parameterized Budget Drop Specifications (`hookStack + 48`) -/

def promotableEvenDropSpecWithStack [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (hookStack : Nat) :
    Spec (BytesDropGhost × M.σ) where
  pre := fun ((ptr, bs, off), st) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) = 0#64 ∧
      s.readReg64 .x0 = (ptr ||| 1#64) ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
    bytesBoxU8Buf A.repAlloc ptr bs ∗
    A.pool lim st s ∗
    stackAt s.sp (hookStack + 48)
  post := fun ((_, bs, _), st) s0 sf =>
    let st' := M.stepEvents (rustDeallocEvents bs.length 1) st
    ⌜sf.trace = s0.trace ∧ M.liveBytes st' ≤ M.liveBytes st⌝ ∗
    A.pool lim st' sf ∗
    stackAt s0.sp (hookStack + 48)

def promotableOddDropSpecWithStack [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (hookStack : Nat) :
    Spec (BytesDropGhost × M.σ) where
  pre := fun ((ptr, bs, off), st) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) ≠ 0#64 ∧
      s.readReg64 .x0 = ptr ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
    bytesBoxU8Buf A.repAlloc ptr bs ∗
    A.pool lim st s ∗
    stackAt s.sp (hookStack + 48)
  post := fun ((_, bs, _), st) s0 sf =>
    let st' := M.stepEvents (rustDeallocEvents bs.length 1) st
    ⌜sf.trace = s0.trace ∧ M.liveBytes st' ≤ M.liveBytes st⌝ ∗
    A.pool lim st' sf ∗
    stackAt s0.sp (hookStack + 48)

def bytesVtableDropSpecWithStack [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (hookStack : Nat) (ptr : BitVec 64)
    (bs : List (BitVec 8)) (off : Nat) : Spec M.σ where
  pre := fun st s =>
    ⌜off ≤ bs.length ∧
      s.readReg64 .x0 = bytesData ptr bs.length ∧
      s.readReg64 .x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
    bytesBoxU8Buf A.repAlloc ptr bs ∗
    A.pool lim st s ∗
    stackAt s.sp (hookStack + 48)
  post := fun st s0 sf =>
    let st' := M.stepEvents (bytesDropEvents bs) st
    ⌜sf.trace = s0.trace ∧ M.liveBytes st' ≤ M.liveBytes st⌝ ∗
    A.pool lim st' sf ∗
    stackAt s0.sp (hookStack + 48)

/-! ## 3. Relocatable `[LibsignalPlacement]` Budget Contracts (Blocks `224`, `236`, `237`) -/

/-- Block `224`: `bytes::bytes::static_drop` meets `bytesStaticDropSpec` (`VmPreserved`)
    under `[LibsignalPlacement]`. -/
theorem bytesStaticDrop_placed_ok [LibsignalPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_224).rebase (blkPl_224).base H) (blkPl_224).base
      bytesStaticDropSpec := by
  unfold bytesStaticDropSpec
  wp_init x s0
  wp_steps
  wp_done

theorem promotableEvenDrop_placed_ok_of_dealloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hdealloc_ext : subroutine_ok ((blkPC_237).rebase (blkPl_237).base H)
      (lsρ lsBytesRustDeallocSym)
      (rustCliDeallocBudgetSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_237).rebase (blkPl_237).base H) (blkPl_237).base
      (promotableEvenDropSpecWithStack M A lim hookStack) := by
  unfold promotableEvenDropSpecWithStack bytesBoxU8Buf
  have hdealloc := deallocBudget_tail_ok_of_dealloc hstack hdealloc_ext
  clear hdealloc_ext
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_add_48_opt hstack]
  cells_unfold
  wp_init x s0
  obtain ⟨⟨ptr, bs, off⟩, st⟩ := x
  dsimp only at *
  have hpos : 0 < bs.length := by assumption
  have hoff : off ≤ bs.length := by assumption
  have heven : (ptr &&& 1#64) = 0#64 := by assumption
  have hlr : LsRetAddr624 (s0.readReg64 .lr) := by assumption
  have hlr30 : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := hlr
  have hlen63 : bs.length < 2 ^ 63 := by assumption
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  simp only [hbs_ne, ↓reduceIte]
  have hand : (ptr ||| 1#64) &&& (-2#64) = ptr := or_one_and_not_one heven
  apply sepWP_seg_ls_vm (Q := (blkPC_237).rebase (blkPl_237).base (hooksException H))
    blkLib_eq_237 (mid := lsρ lsBytesRustDeallocSym)
  intro _m_strip
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_add hoff,
      ult_ofNat_false hoff hlen63] at hcs
    cases hcs
  · wp_steps
    refine SepWP.done (by rfl) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
    have hadd_even' : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_add hoff]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    wp_call hdealloc (ptr, bs, 1, st, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

theorem promotableEvenDrop_placed_ok_withStack [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hle : allocHookStack ≤ hookStack := by decide)
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hdealloc : HookSat H lsBytesRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_237).rebase (blkPl_237).base H) (blkPl_237).base
      (promotableEvenDropSpecWithStack M A lim hookStack) :=
  promotableEvenDrop_placed_ok_of_dealloc hstack
    (subroutine_ok_rustCliDeallocBudget_withStack hle (by omega)
      (ls_hook_ok_rustDealloc hdealloc))

/-- Block `237`: `bytes::bytes::promotable_even_drop` meets `promotableEvenDropSpec`
    under `[LibsignalPlacement]`. -/
theorem promotableEvenDrop_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsBytesRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_237).rebase (blkPl_237).base H) (blkPl_237).base
      (promotableEvenDropSpec M A lim) :=
  promotableEvenDrop_placed_ok_withStack (hookStack := allocHookStack)
    (by decide) (by decide) hdealloc

theorem promotableEvenDrop_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsBytesRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_237).rebase (blkPl_237).base H) (blkPl_237).base
      (promotableEvenDropSpecX M A lim) :=
  promotableEvenDrop_placed_ok_withStack (hookStack := extHookStack)
    (by decide) (by decide) hdealloc

theorem promotableOddDrop_placed_ok_of_dealloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hdealloc_ext : subroutine_ok ((blkPC_236).rebase (blkPl_236).base H)
      (lsρ lsBytesRustDeallocSym)
      (rustCliDeallocBudgetSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_236).rebase (blkPl_236).base H) (blkPl_236).base
      (promotableOddDropSpecWithStack M A lim hookStack) := by
  unfold promotableOddDropSpecWithStack bytesBoxU8Buf
  have hdealloc := deallocBudget_tail_ok_of_dealloc hstack hdealloc_ext
  clear hdealloc_ext
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_add_48_opt hstack]
  cells_unfold
  wp_init x s0
  obtain ⟨⟨ptr, bs, off⟩, st⟩ := x
  dsimp only at *
  have hpos : 0 < bs.length := by assumption
  have hoff : off ≤ bs.length := by assumption
  have hodd : (ptr &&& 1#64) ≠ 0#64 := by assumption
  have hlr : LsRetAddr624 (s0.readReg64 .lr) := by assumption
  have hlr30 : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := hlr
  have hlen63 : bs.length < 2 ^ 63 := by assumption
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  simp only [hbs_ne, ↓reduceIte]
  have hlsb0 : ptr.getLsbD 0 = true := getLsbD_zero_iff.mpr hodd
  apply sepWP_seg_ls_vm (Q := (blkPC_236).rebase (blkPl_236).base (hooksException H))
    blkLib_eq_236 (mid := lsρ lsBytesRustDeallocSym)
  intro _m_strip
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_add hoff,
      ult_ofNat_false hoff hlen63] at hcs
    cases hcs
  · wp_steps
    refine SepWP.done (by rfl) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
    have hadd_odd : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_add hoff]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    wp_call hdealloc (ptr, bs, 1, st, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

theorem promotableOddDrop_placed_ok_withStack [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hle : allocHookStack ≤ hookStack := by decide)
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hdealloc : HookSat H lsBytesRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_236).rebase (blkPl_236).base H) (blkPl_236).base
      (promotableOddDropSpecWithStack M A lim hookStack) :=
  promotableOddDrop_placed_ok_of_dealloc hstack
    (subroutine_ok_rustCliDeallocBudget_withStack hle (by omega)
      (ls_hook_ok_rustDealloc hdealloc))

/-- Block `236`: `bytes::bytes::promotable_odd_drop` meets `promotableOddDropSpec`
    under `[LibsignalPlacement]`. -/
theorem promotableOddDrop_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsBytesRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_236).rebase (blkPl_236).base H) (blkPl_236).base
      (promotableOddDropSpec M A lim) :=
  promotableOddDrop_placed_ok_withStack (hookStack := allocHookStack)
    (by decide) (by decide) hdealloc

theorem promotableOddDrop_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsBytesRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_236).rebase (blkPl_236).base H) (blkPl_236).base
      (promotableOddDropSpecX M A lim) :=
  promotableOddDrop_placed_ok_withStack (hookStack := extHookStack)
    (by decide) (by decide) hdealloc

theorem bytesVtableDrop_placed_ok_of_drops [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {hookStack : Nat}
    (heven_ok : subroutine_ok ((blkPC_237).rebase (blkPl_237).base H) (blkPl_237).base
      (promotableEvenDropSpecWithStack M A lim hookStack))
    (hodd_ok : subroutine_ok ((blkPC_236).rebase (blkPl_236).base H) (blkPl_236).base
      (promotableOddDropSpecWithStack M A lim hookStack))
    (hi : i < 619 := by decide)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok callerProg (bytesPlacedDropFnAddr ptr bs.length)
      (withLsCodeLoaded lsmpl (bytesVtableDropSpecWithStack M A lim hookStack ptr bs off)) := by
  refine subroutine_ok_outcome_intro ?_
  intro st R s0 hpc hrun hpre hsp
  by_cases hbs : bs = []
  · subst hbs
    have haddr : bytesPlacedDropFnAddr ptr ([] : List (BitVec 8)).length = (blkPl_224).base := rfl
    rw [haddr] at hpc
    have hstatic := ls_subroutine_ok_of_block (callerProg := callerProg)
      (subroutine_ok_withLsCodeLoaded_of_plain (bytesStaticDrop_placed_ok H)) hi
    have ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
    unfold bytesVtableDropSpecWithStack bytesBoxU8Buf at hpre0
    simp only [↓reduceIte, sepConj_emp, sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨_, _, hmem⟩
    have hpre_static : s0.mem ⊨ (withLsCodeLoaded lsmpl bytesStaticDropSpec).pre () s0 ∗
        (A.pool lim st s0 ∗ (stackAt s0.sp (hookStack + 48) ∗ R)) := by
      dsimp only [withLsCodeLoaded, bytesStaticDropSpec]
      rw [emp_sepConj, satisfies_pure_sepConj]
      exact ⟨hcl, hmem⟩
    refine hstatic.mono_outcome () (A.pool lim st s0 ∗ (stackAt s0.sp (hookStack + 48) ∗ R))
      s0 hpc hrun hpre_static hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeLoaded, bytesVtableDropSpecWithStack]
      dsimp only [withLsCodeLoaded, bytesStaticDropSpec] at hpost
      rw [satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨⟨htr, hvm⟩, hmem_sf⟩
      have hev0 : M.stepEvents (bytesDropEvents ([] : List (BitVec 8))) st = st := rfl
      rw [hev0, A.pool_transport lim st s0 sf hvm, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨htr, Nat.le_refl _⟩, by simpa only [sepConj_assoc] using hmem_sf⟩
    · exact (not_satisfies_false_sepConj hpost).elim
    · exact (not_satisfies_false_sepConj hpost).elim
    · exact (not_satisfies_false_sepConj hpost).elim
  · have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
    have hlen_ne : bs.length ≠ 0 := by omega
    have hev_ne : bytesDropEvents bs = rustDeallocEvents bs.length 1 := by
      simp [bytesDropEvents, hlen_ne]
    by_cases heven : (ptr &&& 1#64) = 0#64
    · have haddr : bytesPlacedDropFnAddr ptr bs.length = (blkPl_237).base := by
        unfold bytesPlacedDropFnAddr
        simp only [hlen_ne, heven, ↓reduceIte]
        rfl
      rw [haddr] at hpc
      have heven_cl := ls_subroutine_ok_of_block (callerProg := callerProg)
        (subroutine_ok_withLsCodeLoaded_of_plain heven_ok) hi
      have ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
      have hpre_even :
          s0.mem ⊨ (withLsCodeLoaded lsmpl
            (promotableEvenDropSpecWithStack M A lim hookStack)).pre
            ((ptr, bs, off), st) s0 ∗ R := by
        dsimp only [withLsCodeLoaded, bytesVtableDropSpecWithStack, bytesData, bytesPtr] at hpre0
        dsimp only [withLsCodeLoaded, promotableEvenDropSpecWithStack]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        refine ⟨hcl, ?_⟩
        simp only [hlen_ne, heven, ↓reduceIte, sepConj_assoc, satisfies_pure_sepConj] at hpre0
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        rcases hpre0 with ⟨⟨hoff, hx0, hx1, hx2, hlr⟩, hrest⟩
        exact ⟨⟨hpos, hoff, heven, hx0, hx1, hx2, hlr⟩, hrest⟩
      refine heven_cl.mono_outcome ((ptr, bs, off), st) R s0 hpc hrun hpre_even hsp ?_
      rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩)
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [withLsCodeLoaded, bytesVtableDropSpecWithStack]
        dsimp only [withLsCodeLoaded, promotableEvenDropSpecWithStack] at hpost
        rwa [hev_ne]
      · exact (not_satisfies_false_sepConj hpost).elim
      · exact (not_satisfies_false_sepConj hpost).elim
      · exact (not_satisfies_false_sepConj hpost).elim
    · have haddr : bytesPlacedDropFnAddr ptr bs.length = (blkPl_236).base := by
        unfold bytesPlacedDropFnAddr
        simp only [hlen_ne, heven, ↓reduceIte]
        rfl
      rw [haddr] at hpc
      have hodd_cl := ls_subroutine_ok_of_block (callerProg := callerProg)
        (subroutine_ok_withLsCodeLoaded_of_plain hodd_ok) hi
      have ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
      have hpre_odd :
          s0.mem ⊨ (withLsCodeLoaded lsmpl
            (promotableOddDropSpecWithStack M A lim hookStack)).pre
            ((ptr, bs, off), st) s0 ∗ R := by
        dsimp only [withLsCodeLoaded, bytesVtableDropSpecWithStack, bytesData, bytesPtr] at hpre0
        dsimp only [withLsCodeLoaded, promotableOddDropSpecWithStack]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        refine ⟨hcl, ?_⟩
        simp only [hlen_ne, heven, ↓reduceIte, sepConj_assoc, satisfies_pure_sepConj] at hpre0
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        rcases hpre0 with ⟨⟨hoff, hx0, hx1, hx2, hlr⟩, hrest⟩
        exact ⟨⟨hpos, hoff, heven, hx0, hx1, hx2, hlr⟩, hrest⟩
      refine hodd_cl.mono_outcome ((ptr, bs, off), st) R s0 hpc hrun hpre_odd hsp ?_
      rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩)
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [withLsCodeLoaded, bytesVtableDropSpecWithStack]
        dsimp only [withLsCodeLoaded, promotableOddDropSpecWithStack] at hpost
        rwa [hev_ne]
      · exact (not_satisfies_false_sepConj hpost).elim
      · exact (not_satisfies_false_sepConj hpost).elim
      · exact (not_satisfies_false_sepConj hpost).elim

theorem bytesVtableDrop_placed_ok_withStack [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {hookStack : Nat}
    (hle : allocHookStack ≤ hookStack := by decide)
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hdealloc : HookSat H lsBytesRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok callerProg (bytesPlacedDropFnAddr ptr bs.length)
      (withLsCodeLoaded lsmpl (bytesVtableDropSpecWithStack M A lim hookStack ptr bs off)) :=
  bytesVtableDrop_placed_ok_of_drops
    (promotableEvenDrop_placed_ok_withStack hle hstack hdealloc)
    (promotableOddDrop_placed_ok_withStack hle hstack hdealloc)
    hi ptr bs off

/-- Unified relocatable vtable `drop` dispatch (`entry_pc = bytesPlacedDropFnAddr ptr bs.length`)
    meets `bytesVtableDropSpec` for any caller block `i` under `[LibsignalPlacement]`. -/
theorem bytesVtableDrop_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H lsBytesRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok callerProg (bytesPlacedDropFnAddr ptr bs.length)
      (withLsCodeLoaded lsmpl (bytesVtableDropSpec M A lim ptr bs off)) :=
  bytesVtableDrop_placed_ok_withStack (hookStack := allocHookStack)
    (by decide) (by decide) hdealloc hi ptr bs off

theorem bytesVtableDrop_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H lsBytesRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok callerProg (bytesPlacedDropFnAddr ptr bs.length)
      (withLsCodeLoaded lsmpl (bytesVtableDropSpecX M A lim ptr bs off)) :=
  bytesVtableDrop_placed_ok_withStack (hookStack := extHookStack)
    (by decide) (by decide) hdealloc hi ptr bs off

end LibsignalBinary.Proofs.TripleRatchet.Bytes.DropsBudget
