/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessage
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded `SessionState::clear_unacknowledged_pre_key_message` (Block `35`)

Verifies `<SessionState>::clear_unacknowledged_pre_key_message` against `clearUpkSpec M A lim` and
`clearUpkSpecX M A lim` under `[LibsignalPlacement]` over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessageBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.RustHeap
  (RustAlloc allocHookStack vecHeader vecU8At_entails_dealloc)
open CryptoVerification.LibsignalSessionRepr (vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr
  (TailVecGhost noneCap optTailVecAt sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet.Getters
  (ClearUpkGhost blkPC_35 blkPl_35
   lsRustDeallocSym ls_hook_ok_rustDealloc
   sessionStateAt_cleared_upk_intro sessionStateAt_split_upk)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
  (clearUpkSpec clearUpkSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustDeallocExternSpecWithStack rustDeallocExternWithStack_of_rustDealloc)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Stack-parameterized budget specification of `<SessionState>::clear_unacknowledged_pre_key_message`. -/
def clearUpkSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (ClearUpkGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗ A.pool lim st s ∗ stackAt s.sp (32 + hookStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sessionStateAt A.repAlloc x.ss { x.G with pending := none, kyber := none }
        x.st.clearUnacknowledgedPreKeyMessage ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (32 + hookStack)

private theorem slt_one_iff_eq_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap.slt 1#64 = true) ↔ cap = 0 := by
  have h1 : (cap = 0) ↔ cap.toNat = 0 := ⟨by rintro rfl; rfl, fun h0 => BitVec.eq_of_toNat_eq h0⟩
  have h2 : (1#64 : BitVec 64).toNat = 1 := rfl
  have h3 : 2 * cap.toNat < 2 ^ 64 := by omega
  rw [h1]
  unfold BitVec.slt BitVec.toInt
  simp only [decide_eq_true_iff, h2, h3, ↓reduceIte]
  omega

private theorem optTailVecAt_entails_deallocX_local (A : RustAlloc) (size : Nat)
    (hsz24 : 24 ≤ size) (hsz64 : size ≤ 64) (a : BitVec 64) (opt : Option TailVecGhost) :
    optTailVecAt A size a opt ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) (size - 16) ∗
        (if cap.slt 1#64 = true then emp
         else ⌜0 < cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗
           A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  cases opt with
  | none =>
    unfold optTailVecAt
    have hsplit : size - 8 = 8 + (size - 16) := by omega
    rw [hsplit,
        ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := size - 16)
          (b' := a + 16#64) rfl (by bv_omega) (by omega),
        memRegion_eight (a + 8#64),
        sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right noneCap (Entails.sepExists_right ptr ?_)
    have hslt : noneCap.slt 1#64 = true := by decide
    simp only [hslt, ↓reduceIte, sepConj_emp]
    exact Entails.refl _
  | some g =>
    unfold optTailVecAt
    apply Entails.pure_left; intro htail
    have hvec : vecGhostAt A g.vec a ⊢
        (a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else ⌜0 < g.vec.cap.toNat ∧ g.vec.cap.toNat < 2 ^ 63⌝ ∗
             A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat) := by
      unfold vecGhostAt
      refine Entails.trans (vecU8At_entails_dealloc A a g.vec.cap g.vec.ptr g.vec.bytes) ?_
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader
      simp only [slt_one_iff_eq_zero hcap_lt, sepConj_assoc]
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
      by_cases h0 : g.vec.cap = 0
      · simp only [h0, ↓reduceIte]; exact Entails.refl _
      · simp only [h0, ↓reduceIte]
        have hpos : 0 < g.vec.cap.toNat :=
          Nat.pos_of_ne_zero (fun h => h0 (BitVec.eq_of_toNat_eq h))
        exact Entails.pure_right ⟨hpos, hcap_lt⟩ (Entails.refl _)
    refine Entails.trans (sepConj_mono_left hvec) ?_
    refine Entails.sepExists_right g.vec.cap (Entails.sepExists_right g.vec.ptr ?_)
    have h16 :
        (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ ((a + 24#64) ↦ₛ g.tail)) ⊢
          memRegion (a + 16#64) (size - 16) := by
      have hsplit : size - 16 = 8 + (size - 24) := by omega
      rw [hsplit,
          ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := size - 24)
            (b' := a + 24#64) rfl (by bv_omega) (by omega)]
      apply sepConj_mono (pointsTo64_entails_memRegion _ _)
      have hb := pointsToBytes_entails_memRegion (a + 24#64) g.tail
      rwa [htail] at hb
    have hpull1 :
        (((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else ⌜0 < g.vec.cap.toNat ∧ g.vec.cap.toNat < 2 ^ 63⌝ ∗
             A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat)) ∗
          ((a + 24#64) ↦ₛ g.tail)) =
        ((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ ((a + 24#64) ↦ₛ g.tail)) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else ⌜0 < g.vec.cap.toNat ∧ g.vec.cap.toNat < 2 ^ 63⌝ ∗
             A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat)) := by
      sep_ac_rfl
    rw [hpull1]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h16))

private theorem stackAt_clearUpk_placed {hookStack : Nat}
    (hstack : hookStack + 32 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (32 + hookStack) = stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 := by
  rw [Nat.add_comm 32 hookStack]
  exact stackAt_split_cells sp hookStack 4 hstack

@[local wp_norm] private theorem exists_two_pow_one_placed : (∃ k : Nat, 1 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨0, rfl⟩

private theorem freeOnlyEvs_rustDeallocEvents_one (sz : Nat) :
    FreeOnlyEvs (rustDeallocEvents sz 1) := by
  simpa [rustDeallocEvents] using FreeOnlyEvs.singleton 1 sz

private theorem clearUpk_strengthen_post_budget {prog : Program} {target_pc : BitVec 64} {s : State}
    {P R : SepProp} {S₁ S₂ : SepProp}
    {PostRest : State → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → List AllocEvent → SepProp}
    {traceProp : State → Prop} {rest : State → Prop}
    (himp : S₁ ⊢ S₂)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ∃∗ evs,
          ⌜traceProp sf⌝ ∗ S₁ ∗ PostRest sf x x_1 x_2 x_3 evs) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ∃∗ evs,
          ⌜traceProp sf⌝ ∗ S₂ ∗ PostRest sf x x_1 x_2 x_3 evs) ∧ rest sf) := by
  refine SepWP.mono h fun sf _ _ _ ⟨h1, h2⟩ => ⟨fun hm => ?_, h2⟩
  refine Satisfies.mono ?_ (h1 hm)
  apply Entails.sepExists_elim; intro x; refine Entails.sepExists_right x ?_
  apply Entails.sepExists_elim; intro x_1; refine Entails.sepExists_right x_1 ?_
  apply Entails.sepExists_elim; intro x_2; refine Entails.sepExists_right x_2 ?_
  apply Entails.sepExists_elim; intro x_3; refine Entails.sepExists_right x_3 ?_
  apply Entails.sepExists_elim; intro evs; refine Entails.sepExists_right evs ?_
  exact sepConj_mono_right (sepConj_mono_left himp)

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
/-- Block `35`: `SessionState::clear_unacknowledged_pre_key_message` meets
    `clearUpkSpecWithStack M A lim hookStack` under `[LibsignalPlacement]`. -/
theorem clear_unacknowledged_pre_key_message_placed_ok_of_dealloc [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) (hookStack : Nat)
    (hstack : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hdealloc : subroutine_ok ((blkPC_35).rebase (blkPl_35).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_35).rebase (blkPl_35).base H) (blkPl_35).base
      (clearUpkSpecWithStack M A lim hookStack) := by
  unfold clearUpkSpecWithStack
  simp only [rustDeallocExternSpecWithStack,
    _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hdealloc
  wp_init x s0
  rcases x with ⟨⟨ss, G, sessSt⟩, st⟩
  dsimp only at *
  subst h
  rw [sessionStateAt_split_upk, stackAt_clearUpk_placed (by omega) s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.pure_elim ?_
  rintro ⟨hloc, hrem, hchains, hpending, hreg, hlik_len, hrik_len⟩
  refine SepWP.weaken_pre
    (sepConj_mono
      (optTailVecAt_entails_deallocX_local A.repAlloc 48 (by decide) (by decide)
        (s0.readReg64 (Reg.gpr 0#5) + 0xf8#64) G.pending)
      (sepConj_mono_left
        (optTailVecAt_entails_deallocX_local A.repAlloc 32 (by decide) (by decide)
          (s0.readReg64 (Reg.gpr 0#5) + 0x128#64) G.kyber))) ?_
  wp_pull_exists
  rename_i cap2 ptr2 cap1 ptr1
  refine clearUpk_strengthen_post_budget
    (sessionStateAt_cleared_upk_intro A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) ptr1 ptr2 G sessSt
      hloc hrem hchains hreg hlik_len hrik_len) ?_
  by_cases h1 : cap1.slt 1#64 = true <;>
    by_cases h2 : cap2.slt 1#64 = true <;>
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj,
      RustCliAllocBudget.repAlloc_live]
  · wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    rw [← M.stepEvents_nil st]
    have hfree0 : FreeOnlyEvs ([] : List AllocEvent) := FreeOnlyEvs.nil
    wp_done
  · refine SepWP.focus_pure (by sep_focus) ?_
    rintro ⟨hpos2, hlt2⟩
    have hrlay2 : RustLayoutOk cap2.toNat 1 := ⟨⟨hpos2, ⟨0, rfl⟩, by omega⟩, by decide⟩
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc (ptr2, cap2.toNat, 1, st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    have hfree2 : FreeOnlyEvs (rustDeallocEvents cap2.toNat 1) :=
      freeOnlyEvs_rustDeallocEvents_one cap2.toNat
    wp_done
  · refine SepWP.focus_pure (by sep_focus) ?_
    rintro ⟨hpos1, hlt1⟩
    have hrlay1 : RustLayoutOk cap1.toNat 1 := ⟨⟨hpos1, ⟨0, rfl⟩, by omega⟩, by decide⟩
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc (ptr1, cap1.toNat, 1, st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    have hfree1 : FreeOnlyEvs (rustDeallocEvents cap1.toNat 1) :=
      freeOnlyEvs_rustDeallocEvents_one cap1.toNat
    wp_done
  · refine SepWP.focus_pure (by sep_focus) ?_
    rintro ⟨hpos1, hlt1⟩
    refine SepWP.focus_pure (by sep_focus) ?_
    rintro ⟨hpos2, hlt2⟩
    have hrlay1 : RustLayoutOk cap1.toNat 1 := ⟨⟨hpos1, ⟨0, rfl⟩, by omega⟩, by decide⟩
    have hrlay2 : RustLayoutOk cap2.toNat 1 := ⟨⟨hpos2, ⟨0, rfl⟩, by omega⟩, by decide⟩
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc (ptr1, cap1.toNat, 1, st)
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc (ptr2, cap2.toNat, 1, M.stepEvents (rustDeallocEvents cap1.toNat 1) st)
    rw [hsp_sf]
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    rw [← M.stepEvents_append]
    have hfree12 : FreeOnlyEvs (rustDeallocEvents cap1.toNat 1 ++ rustDeallocEvents cap2.toNat 1) :=
      FreeOnlyEvs.append
        (freeOnlyEvs_rustDeallocEvents_one cap1.toNat)
        (freeOnlyEvs_rustDeallocEvents_one cap2.toNat)
    wp_done

/-- Block `35`: `SessionState::clear_unacknowledged_pre_key_message` meets `clearUpkSpec M A lim`
    under `[LibsignalPlacement]`. -/
theorem clear_unacknowledged_pre_key_message_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_35).rebase (blkPl_35).base H) (blkPl_35).base
      (clearUpkSpec M A lim) :=
  clear_unacknowledged_pre_key_message_placed_ok_of_dealloc A lim H allocHookStack (by decide)
    (rustDeallocExternWithStack_of_rustDealloc (by decide) (by decide)
      (ls_hook_ok_rustDealloc hdealloc))

/-- Block `35`: `SessionState::clear_unacknowledged_pre_key_message` meets `clearUpkSpecX M A lim`
    under `[LibsignalPlacement]`. -/
theorem clear_unacknowledged_pre_key_message_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_35).rebase (blkPl_35).base H) (blkPl_35).base
      (clearUpkSpecX M A lim) :=
  clear_unacknowledged_pre_key_message_placed_ok_of_dealloc A lim H extHookStack (by decide)
    (rustDeallocExternWithStack_of_rustDealloc (by decide) (by decide)
      (ls_hook_ok_rustDealloc hdealloc))

end LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessageBudget
