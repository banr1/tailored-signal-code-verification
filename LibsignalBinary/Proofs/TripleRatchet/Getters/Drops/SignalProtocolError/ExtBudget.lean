/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Ext
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable Contract for `drop_glue<SignalProtocolError>`

Proves the `RustCliAllocBudget`-threaded `[LibsignalPlacement]` contract `dropSpeSpec`
for `core::ptr::drop_glue::<SignalProtocolError>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  LibsignalHooks LibsignalPlacement LibsignalRoLoaded
  lsroCheck lsro_intro_chk lsmpl lsρ
)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  SatEntails blkPC_5 blkPl_5 dropSpeStack lsRustDeallocSym ls_hook_ok_rustDealloc
  speJumpTable speJumpTableSym withLsRoLoaded
  spe_str_pre_weaken spe_unit_pre_weaken spe_tail_dealloc_pre_weaken
  speAt_invalidState_expose speAt_invalidMessage_expose
  spe_u64_at_8_entails_40 spe_u8_at_8_entails_40
  spe_strRef_at_8_entails_40 spe_u32x2_at_8_entails_40
)
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts (
  spe_str_cap0_pre_weaken_full spe_noop_pre_weaken_full spe_tail_dealloc_post
  stackAt_dropSpe_split
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
  rustDeallocEvents rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpec)

attribute [local irreducible] Program.fetch Program.externAt?

private theorem SepWP.false_elim {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  have heq : (P ∗ ⌜False⌝ ∗ Q) ∗ R = ⌜False⌝ ∗ (P ∗ Q ∗ R) := by sep_ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact False.elim hm.1

private theorem lsroCheck_speJumpTable : lsroCheck speJumpTableSym speJumpTable = true := by
  exact eagerReduce (Eq.refl true)

private theorem intro_lsro_speJumpTable [LibsignalPlacement]
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWP prog target_pc s (((lsρ speJumpTableSym) ↦ᵣ speJumpTable) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  have hR := h R
  rw [sepConj_assoc] at hR
  exact hR (lsro_intro_chk hro lsroCheck_speJumpTable hm)

private theorem speJumpTable_placed_byte (base : BitVec 64) (i : Nat) (b : BitVec 8)
    (heq : speJumpTable = speJumpTable.take i ++ (b :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i) :
    SatEntails (base ↦ᵣ speJumpTable) ((base + BitVec.ofNat 64 i) ↦₈ᵣ b) := by
  have h : (base ↦ᵣ speJumpTable) =
      (base ↦ᵣ speJumpTable.take i) ∗
        (((base + BitVec.ofNat 64 i) ↦₈ᵣ b) ∗
         ((base + BitVec.ofNat 64 i + 1#64) ↦ᵣ speJumpTable.drop (i + 1))) := by
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen]
  rw [h]
  exact SatEntails.trans (SatEntails.drop_left _ _) (SatEntails.drop_right _ _)

private theorem freeOnlyPool_nil {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (sf : State) :
    A.pool lim st sf ⊢
      ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf :=
  Entails.sepExists_right [] (Entails.pure_right FreeOnlyEvs.nil (Entails.refl _))

private theorem freeOnlyPool_dealloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (sz al : Nat) (sf : State) :
    A.pool lim (M.stepEvents (rustDeallocEvents sz al) st) sf ⊢
      ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf :=
  Entails.sepExists_right (rustDeallocEvents sz al)
    (Entails.pure_right (FreeOnlyEvs.singleton al sz) (Entails.refl _))

private theorem spe_str_cap0_budget (pool : SepProp) (a w cap ptr sp fp lr x20 x19 : BitVec 64)
    (ro : SepProp) :
    SatEntails
      (pool ∗ (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ro ∗ stackAt (sp - 32#64) CryptoVerification.RustHeap.allocHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStack) :=
  SatEntails.trans (SatEntails.of_eq (by sep_ac_rfl))
    (spe_str_cap0_pre_weaken_full a w cap ptr sp fp lr x20 x19 ro pool)

private theorem spe_noop_budget (pool : SepProp) (a w sp fp lr x20 x19 : BitVec 64)
    (ro : SepProp) :
    SatEntails
      (pool ∗ (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro ∗
        stackAt (sp - 32#64) CryptoVerification.RustHeap.allocHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStack) :=
  SatEntails.trans (SatEntails.of_eq (by sep_ac_rfl))
    (spe_noop_pre_weaken_full a w sp fp lr x20 x19 ro pool)

private theorem spe_tail_dealloc_budget (pool : SepProp)
    (a w cap ptr sp fp lr x20 x19 : BitVec 64) (ro live1 live2 : SepProp) :
    SatEntails
      (pool ∗ (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ro ∗ live1 ∗ live2 ∗
        stackAt (sp - 32#64) CryptoVerification.RustHeap.allocHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ memRegion (sp - 4128#64) 32 ∗
        stackAt sp CryptoVerification.RustHeap.allocHookStack ∗ live1 ∗ live2) :=
  SatEntails.trans (SatEntails.of_eq (by sep_ac_rfl))
    (SatEntails.trans (spe_tail_dealloc_pre_weaken a w cap ptr sp fp lr x20 x19 ro (live1 ∗ live2) pool)
      (SatEntails.of_eq (by sep_ac_rfl)))

theorem drop_spe_placed_ok_of_dealloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_5).rebase (blkPl_5).base H) (blkPl_5).base
      (withLsRoLoaded lsmpl (dropSpeSpec M A lim)) := by
  simp only [withLsRoLoaded, dropSpeSpec, pure_sepConj_pure_assoc]
  simp only [rustCliDeallocBudgetSpec] at hdealloc
  wp_init x s0
  rcases x with ⟨⟨a, fnName, e⟩, st⟩
  dsimp only at *
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = a := by assumption
  subst hx0
  have hro : LibsignalRoLoaded lsmpl s0.mem := by assumption
  refine intro_lsro_speJumpTable hro ?_
  nth_rw 1 [stackAt_dropSpe_split s0.sp]
  cells_unfold
  wp_pull_exists
  cases e with
  | panic =>
    simp only [speAt]
    exact SepWP.false_elim
  | invalidState =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_str_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidState
        1 0x8000000000000001#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 1 0x00#8 rfl rfl)
        (speAt_invalidState_expose A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5))) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      simp only [State.setMem_setMem]
      refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
        (spe_str_cap0_budget _ _ _ _ _ s0.sp _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      simp only [State.setMem_setMem]
      refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
        (spe_tail_dealloc_budget _ (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _) ?_
      wp_call hdealloc (ptr, cap.toNat, 1, st)
      have htr_d : sf.trace = s0.trace := ‹AllocCallPreserved _ sf›.2.1
      refine SepWP.weaken_pre
        (spe_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) (A.pool lim _ sf) s0.sp) ?_
      apply SepWP.fold (freeOnlyPool_dealloc A lim st cap.toNat 1 sf) (by sep_focus)
      wp_done
  | invalidMessage t r =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_str_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidMessage t r)
        24 0x8000000000000018#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 24 0x00#8 rfl rfl)
        (speAt_invalidMessage_expose A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) t r) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      simp only [State.setMem_setMem]
      refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
        (spe_str_cap0_budget _ _ _ _ _ s0.sp _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      simp only [State.setMem_setMem]
      refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
        (spe_tail_dealloc_budget _ (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _) ?_
      wp_call hdealloc (ptr, cap.toNat, 1, st)
      have htr_d : sf.trace = s0.trace := ‹AllocCallPreserved _ sf›.2.1
      refine SepWP.weaken_pre
        (spe_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) (A.pool lim _ sf) s0.sp) ?_
      apply SepWP.fold (freeOnlyPool_dealloc A lim st cap.toNat 1 sf) (by sep_focus)
      wp_done
  | invalidProtobufEncoding =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidProtobufEncoding
        2 0x8000000000000002#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 2 0x1b#8 rfl rfl) (SatEntails.refl _) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budget _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | ciphertextMessageTooShort n =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.ciphertextMessageTooShort n)
        3 0x8000000000000003#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 3 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budget _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | legacyCiphertextVersion v =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.legacyCiphertextVersion v)
        4 0x8000000000000004#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 4 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budget _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | unrecognizedCiphertextVersion v =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.unrecognizedCiphertextVersion v)
        5 0x8000000000000005#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 5 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budget _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | noKeyTypeIdentifier =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) .noKeyTypeIdentifier
        7 0x8000000000000007#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 7 0x1b#8 rfl rfl) (SatEntails.refl _) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budget _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | badKeyType t =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyType t)
        8 0x8000000000000008#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 8 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budget _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | badKeyLength n =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyLength n)
        9 0x8000000000000009#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 9 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budget _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | invalidKeyAgreement =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidKeyAgreement
        10 0x800000000000000a#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 10 0x1b#8 rfl rfl) (SatEntails.refl _) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budget _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | invalidSessionStructure r =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidSessionStructure r)
        20 0x8000000000000014#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 20 0x1b#8 rfl rfl)
        (by simp only [speAt]; exact SatEntails.sepConj_mono_right (spe_strRef_at_8_entails_40 _ _)) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budget _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | duplicatedMessage idx c =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.duplicatedMessage idx c)
        23 0x8000000000000017#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 23 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u32x2_at_8_entails_40 _ _ _))) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budget _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done

theorem drop_spe_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_5).rebase (blkPl_5).base H) (blkPl_5).base
      (withLsRoLoaded lsmpl (dropSpeSpec M A lim)) :=
  drop_spe_placed_ok_of_dealloc (ls_hook_ok_rustDealloc h_dealloc)

end LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudget
