/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropsMessageKeyExt
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
import GeneratedLean.LibsignalTripleRatchet -- shake: keep

/-!
# Budget-Threaded `drop_glue::<Vec<MessageKey>>` (Block `3`)

Defines `freePool` combinators for `FreeOnlyEvs`-evolved `RustCliAllocBudget` pools and verifies
relocatable `core::ptr::drop_glue::<Vec<session_structure::Chain::MessageKey>>` (Block `3`) against
`dropVecMessageKeySpecX M A lim`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropsMessageKeyExtBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (MessageKeyGenerator)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl
  lsρ lsRustDeallocSym sepWP_seq_lscl
)
open CryptoVerification.RustHeap (RustAlloc LayoutOk vecAt arrayAt)
open CryptoVerification.LibsignalSessionRepr (MessageKeyGhost VecPin messageKeyAt)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack ls_subroutine_ok_cl_of_callee
)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  blkPC_3 blkPl_3 dropVecMessageKeyStackX
)
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts (
  mkHeadersAt mkHeadersAt_entails_memRegion_104 post_loop_weaken
  vecAt_expose_loop sep_pull_body sep_push_body sep_rejoin_loop
  tail_len_mul_lt ofNat_succ_eq_add_one ofNat_add_one_beq_one_false
  ofNat_beq_zero_false add_104_add_48 cons_len_mul
)
open Proofs.libsignal.Stage1X (lscall_of_withLsCl)
open Proofs.libsignal.Hooks2 (
  stackAt_dropVecMessageKeyX_split cap0_weaken_48_extHook
  tail_dealloc_pre_weaken_ext tail_dealloc_post_48_extHook
  layoutOk_u8_x layoutOk_mul104_x vecPinDeallocX messageKeyAt_entails_deallocX
  SepWP.align_pre_gen
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk
  rustDeallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliDeallocBudgetExternSpecWithStack)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropVecMessageKeySpecX)

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero

/-! ## `freePool` combinators for `FreeOnlyEvs`-evolved drop glue -/

/-- State-indexed existential `FreeOnlyEvs`-evolved budget pool. -/
def freePool {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s

theorem freePool_intro {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ freePool A lim st s := by
  refine Entails.sepExists_right [] ?_
  rw [M.stepEvents_nil]
  exact Entails.pure_right FreeOnlyEvs.nil (Entails.refl _)

theorem freePool_of_evs {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs) (s : State) :
    A.pool lim (M.stepEvents evs st) s ⊢ freePool A lim st s :=
  Entails.sepExists_right evs (Entails.pure_right hevs (Entails.refl _))

theorem freePool_step_dealloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    (sz align : Nat) (s : State) :
    A.pool lim (M.stepEvents (rustDeallocEvents sz align) (M.stepEvents evs st)) s ⊢
      freePool A lim st s := by
  refine Entails.sepExists_right (evs ++ rustDeallocEvents sz align) ?_
  rw [M.stepEvents_append]
  exact Entails.pure_right (FreeOnlyEvs.append hevs (FreeOnlyEvs.singleton align sz)) (Entails.refl _)

theorem freePool_step_sub {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs₁ : List AllocEvent} (hevs₁ : FreeOnlyEvs evs₁)
    (s : State) :
    freePool A lim (M.stepEvents evs₁ st) s ⊢ freePool A lim st s := by
  apply Entails.sepExists_elim; intro evs₂
  apply Entails.pure_left; intro hevs₂
  refine Entails.sepExists_right (evs₁ ++ evs₂) ?_
  rw [M.stepEvents_append]
  exact Entails.pure_right (FreeOnlyEvs.append hevs₁ hevs₂) (Entails.refl _)

theorem seq_clean_lscl_mk_st [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post := by
  apply sepWP_seq_lscl hcl (mid := mid)
  refine SepWP.mono h1 ?_
  rintro sm Pm hpcm hrunm ⟨hent, hQ⟩ hclm
  exact SepWP.weaken_pre hent (h2 sm hpcm hrunm hclm hQ)

theorem sepWP_elim_freePool {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {prog : Program} {target : BitVec 64}
    {s : State} {L R : SepProp} {post : State → SepProp → Prop}
    (h : ∀ evs : List AllocEvent, FreeOnlyEvs evs →
      SepWP prog target s (L ∗ A.pool lim (M.stepEvents evs st) s ∗ R) post) :
    SepWP prog target s (L ∗ freePool A lim st s ∗ R) post := by
  unfold freePool
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun evs => ?_
  have hEq : (L ∗ (⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s) ∗ R) =
      ⌜FreeOnlyEvs evs⌝ ∗ (L ∗ A.pool lim (M.stepEvents evs st) s ∗ R) := by sep_ac_rfl
  rw [hEq]
  exact SepWP.pure_elim (h evs)

private theorem weaken_pool_to_freePool_front {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {s : State} {R : SepProp} :
    A.pool lim (M.stepEvents evs st) s ∗ R ⊢ freePool A lim st s ∗ R :=
  sepConj_mono_left (freePool_of_evs A lim st hevs s)

private theorem weaken_dealloc_to_freePool_front {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {sz align : Nat} {s : State} {R : SepProp} :
    A.pool lim (M.stepEvents (rustDeallocEvents sz align) (M.stepEvents evs st)) s ∗ R ⊢
      freePool A lim st s ∗ R :=
  sepConj_mono_left (freePool_step_dealloc A lim st hevs sz align s)

private theorem align_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  heq ▸ h

/-! ## Block `3` verification -/

/-- Callee-saved registers not saved in `[sp..sp+48]` when `x19..x22, x29, x30` are saved on stack. -/
@[reducible]
private def Saved48Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem expose_pin_deallocX_zero {A : RustAlloc} {pin : VecPin}
    (hcap : (pin.cap == 0#64) = true) :
    vecPinDeallocX A pin = emp := by
  unfold vecPinDeallocX; simp [hcap]

private theorem expose_pin_deallocX {A : RustAlloc} {pin : VecPin}
    (hcap : ¬ (pin.cap == 0#64) = true) :
    vecPinDeallocX A pin =
      ⌜pin.cap.toNat < 2 ^ 63⌝ ∗ (A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat) := by
  unfold vecPinDeallocX; simp [hcap]

private theorem pull_mk_pure4 {φ : Prop} {H P R1 R2 : SepProp} :
    (H ∗ (⌜φ⌝ ∗ P) ∗ R1) ∗ R2 = ⌜φ⌝ ∗ ((H ∗ P ∗ R1) ∗ R2) := by
  sep_ac_rfl

private theorem pull_mk_pure3 {φ : Prop} {H P R2 : SepProp} :
    (H ∗ (⌜φ⌝ ∗ P)) ∗ R2 = ⌜φ⌝ ∗ ((H ∗ P) ∗ R2) := by
  sep_ac_rfl

private theorem rustLayoutOk_u8_of_ne_zero {cap : BitVec 64}
    (hcap : ¬ (cap == 0#64) = true) (hlt : cap.toNat < 2 ^ 63) :
    RustLayoutOk cap.toNat 1 := by
  refine ⟨layoutOk_u8_x ?_ hlt, by decide⟩
  intro h0
  apply hcap
  have heq : cap = 0#64 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  subst heq; rfl

private theorem drop_vec_message_key_placed_body_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H) (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)))
    (s0 : State) (fsp v ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (st : M.σ) :
    ∀ (cur cnt : BitVec 64) (pin : MessageKeyGhost) (mk : MessageKeyGenerator) (s : State) (Frame : SepProp),
      s.pc = (blkPl_3).base + 48#64 → s.status = .Running → LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp → s.readReg64 .x19 = ptr → s.readReg64 .x20 = v →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 48#64 →
      SepWP ((blkPC_3).rebase (blkPl_3).base H) ((blkPl_3).base + 36#64) s
        (messageKeyAt A.repAlloc (pin, mk) cur ∗ freePool A lim st s ∗ stackAt fsp extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗ freePool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) := by
  intro cur cnt pin mk s Frame hpc hrun hcl hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (messageKeyAt_entails_deallocX A.repAlloc cur pin mk)) ?_
  refine seq_clean_lscl_mk_st hcl (mid := (blkPl_3).base + 68#64) (P_mid := fun sm =>
    (mkHeadersAt cur pin ∗ vecPinDeallocX A.repAlloc pin.mac ∗
      vecPinDeallocX A.repAlloc pin.iv ∗ vecPinDeallocX A.repAlloc pin.seed) ∗
    freePool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) ?_ ?_
  · refine sepWP_elim_freePool fun evs hevs => ?_
    by_cases hcap : (pin.cipher.cap == 0#64) = true
    · conv => arg 4; rw [expose_pin_deallocX_zero hcap, emp_sepConj]; dsimp only [mkHeadersAt]
      wp_steps_sync_pool ((blkPl_3).base + 68#64)
      refine SepWP.weaken_pre (weaken_pool_to_freePool_front hevs) ?_
      refine align_pre_st (by dsimp only [mkHeadersAt]; sep_ac_rfl) ?_
      wp_done
    · conv => arg 4; rw [expose_pin_deallocX hcap, pull_mk_pure4]; dsimp only [mkHeadersAt]
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hlayout := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
      apply sepWP_seq_lscl hcl (mid := lsρ lsRustDeallocSym)
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
      have hcall := lscall_of_withLsCl
        (hdealloc : subroutine_ok _ _ (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack))) hcl_c
      have : A.repAlloc.live = A.live := rfl
      rw [this]
      have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      wp_call hcall (pin.cipher.ptr, pin.cipher.cap.toNat, 1, M.stepEvents evs st)
      refine SepWP.weaken_pre (weaken_dealloc_to_freePool_front hevs) ?_
      refine align_pre_st (by dsimp only [mkHeadersAt]; rw [hsp]; sep_ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
    refine seq_clean_lscl_mk_st hcl1 (mid := (blkPl_3).base + 88#64) (P_mid := fun sm =>
      (mkHeadersAt cur pin ∗ vecPinDeallocX A.repAlloc pin.iv ∗ vecPinDeallocX A.repAlloc pin.seed) ∗
      freePool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) ?_ ?_
    · refine sepWP_elim_freePool fun evs hevs => ?_
      by_cases hcap : (pin.mac.cap == 0#64) = true
      · conv => arg 4; rw [expose_pin_deallocX_zero hcap, emp_sepConj]; dsimp only [mkHeadersAt]
        wp_steps_sync_pool ((blkPl_3).base + 88#64)
        refine SepWP.weaken_pre (weaken_pool_to_freePool_front hevs) ?_
        refine align_pre_st (by dsimp only [mkHeadersAt]; sep_ac_rfl) ?_
        wp_done
      · conv => arg 4; rw [expose_pin_deallocX hcap, pull_mk_pure4]; dsimp only [mkHeadersAt]
        refine SepWP.pure_elim fun hcap_lt => ?_
        have hlayout := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
        apply sepWP_seq_lscl hcl1 (mid := lsρ lsRustDeallocSym)
        wp_steps_sync_pool (lsρ lsRustDeallocSym)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
        have hcall := lscall_of_withLsCl
          (hdealloc : subroutine_ok _ _ (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack))) hcl_c
        have : A.repAlloc.live = A.live := rfl
        rw [this]
        have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
        wp_call hcall (pin.mac.ptr, pin.mac.cap.toNat, 1, M.stepEvents evs st)
        refine SepWP.weaken_pre (weaken_dealloc_to_freePool_front hevs) ?_
        refine align_pre_st (by dsimp only [mkHeadersAt]; rw [hsp_1]; sep_ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine seq_clean_lscl_mk_st hcl2 (mid := (blkPl_3).base + 108#64) (P_mid := fun sm =>
        (mkHeadersAt cur pin ∗ vecPinDeallocX A.repAlloc pin.seed) ∗
        freePool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame)
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) ?_ ?_
      · refine sepWP_elim_freePool fun evs hevs => ?_
        by_cases hcap : (pin.iv.cap == 0#64) = true
        · conv => arg 4; rw [expose_pin_deallocX_zero hcap, emp_sepConj]; dsimp only [mkHeadersAt]
          wp_steps_sync_pool ((blkPl_3).base + 108#64)
          refine SepWP.weaken_pre (weaken_pool_to_freePool_front hevs) ?_
          refine align_pre_st (by dsimp only [mkHeadersAt]; sep_ac_rfl) ?_
          wp_done
        · conv => arg 4; rw [expose_pin_deallocX hcap, pull_mk_pure4]; dsimp only [mkHeadersAt]
          refine SepWP.pure_elim fun hcap_lt => ?_
          have hlayout := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
          apply sepWP_seq_lscl hcl2 (mid := lsρ lsRustDeallocSym)
          wp_steps_sync_pool (lsρ lsRustDeallocSym)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
          have hcall := lscall_of_withLsCl
            (hdealloc : subroutine_ok _ _ (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack))) hcl_c
          have : A.repAlloc.live = A.live := rfl
          rw [this]
          have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
          wp_call hcall (pin.iv.ptr, pin.iv.cap.toNat, 1, M.stepEvents evs st)
          refine SepWP.weaken_pre (weaken_dealloc_to_freePool_front hevs) ?_
          refine align_pre_st (by dsimp only [mkHeadersAt]; rw [hsp_2]; sep_ac_rfl) ?_
          wp_done
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        have hstep4 : SepWP ((blkPC_3).rebase (blkPl_3).base H)
            ((blkPl_3).base + 36#64) s3
            ((mkHeadersAt cur pin ∗ vecPinDeallocX A.repAlloc pin.seed) ∗
              freePool A lim st s3 ∗ stackAt fsp extHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ mkHeadersAt cur pin ∗ freePool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) := by
          refine sepWP_elim_freePool fun evs hevs => ?_
          by_cases hcap : (pin.seed.cap == 0#64) = true
          · conv => arg 4; rw [expose_pin_deallocX_zero hcap, sepConj_emp]; dsimp only [mkHeadersAt]
            wp_steps_sync_pool ((blkPl_3).base + 36#64)
            refine SepWP.weaken_pre (weaken_pool_to_freePool_front hevs) ?_
            refine align_pre_st (by dsimp only [mkHeadersAt]; sep_ac_rfl) ?_
            wp_done
          · conv => arg 4; rw [expose_pin_deallocX hcap, pull_mk_pure3]; dsimp only [mkHeadersAt]
            refine SepWP.pure_elim fun hcap_lt => ?_
            have hlayout := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
            apply sepWP_seq_lscl hcl3 (mid := lsρ lsRustDeallocSym)
            wp_steps_sync_pool (lsρ lsRustDeallocSym)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
            have hcall := lscall_of_withLsCl
              (hdealloc : subroutine_ok _ _ (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack))) hcl_c
            have : A.repAlloc.live = A.live := rfl
            rw [this]
            have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
            wp_call hcall (pin.seed.ptr, pin.seed.cap.toNat, 1, M.stepEvents evs st)
            wp_steps_sync_pool ((blkPl_3).base + 36#64)
            refine SepWP.weaken_pre
              (sepConj_mono_left (freePool_step_dealloc A lim st hevs pin.seed.cap.toNat 1 _)) ?_
            refine align_pre_st (by dsimp only [mkHeadersAt]; rw [hsp_3]; sep_ac_rfl) ?_
            wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (mkHeadersAt_entails_memRegion_104 cur pin)), h.2⟩)

private theorem drop_vec_message_key_placed_loop_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H) (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)))
    (s0 : State) (fsp v ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (st : M.σ) :
    ∀ (rest : List (MessageKeyGhost × MessageKeyGenerator)) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 104 < 2 ^ 63 →
      s.pc = (blkPl_3).base + 48#64 → s.status = .Running → LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp → s.readReg64 .x19 = ptr → s.readReg64 .x20 = v →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 48#64 →
      SepWP ((blkPC_3).rebase (blkPl_3).base H) ((blkPl_3).base + 132#64) s
        (arrayAt (messageKeyAt A.repAlloc) 104 cur rest ∗ freePool A lim st s ∗ stackAt fsp extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ freePool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v) := by
  have hbody := drop_vec_message_key_placed_body_ext hdealloc s0 fsp v ptr hfsp_align st
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨pin, mk⟩
    intro cur s Frame _ hlen hpc hrun hcl hpres hx19 hx20 hx21 hx22
    rw [show arrayAt (messageKeyAt A.repAlloc) 104 cur ((pin, mk) :: tl) =
          messageKeyAt A.repAlloc (pin, mk) cur ∗ arrayAt (messageKeyAt A.repAlloc) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine seq_clean_lscl_mk_st hcl (mid := (blkPl_3).base + 36#64)
      (hbody cur (BitVec.ofNat 64 ((pin, mk) :: tl).length) pin mk s
        (arrayAt (messageKeyAt A.repAlloc) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hcl hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 hcl4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4, hx21_4, hx22_4⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx21_4 ⊢
      refine sepWP_elim_freePool fun evs hevs => ?_
      wp_steps_sync_pool ((blkPl_3).base + 132#64)
      refine SepWP.weaken_pre (weaken_pool_to_freePool_front hevs) ?_
      wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show ((pin, mk) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx21_4
      have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
      refine sepWP_elim_freePool fun evs hevs => ?_
      apply sepWP_seq_lscl hcl4 (mid := (blkPl_3).base + 48#64)
      wp_steps_sync_pool ((blkPl_3).base + 48#64)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcl5
      refine SepWP.weaken_pre (weaken_pool_to_freePool_front hevs) ?_
      refine SepWP.align_pre_gen
        (P' := arrayAt (messageKeyAt A.repAlloc) 104 (cur + 104#64) (hd2 :: tl2) ∗
          freePool A lim st _ ∗ stackAt fsp extHookStack ∗ (memRegion cur 104 ∗ Frame))
        (by sep_ac_rfl) ?_
      refine SepWP.mono
        (ih (cur + 104#64) _ (memRegion cur 104 ∗ Frame)
          htl_ne htl_len (by wp_norm_goal) (by wp_norm_lhs) hcl5
          ⟨by simp only [wp_norm, arm64_norm, hx23_4],
           by simp only [wp_norm, arm64_norm, hx24_4],
           by simp only [wp_norm, arm64_norm, hx25_4],
           by simp only [wp_norm, arm64_norm, hx26_4],
           by simp only [wp_norm, arm64_norm, hx27_4],
           by simp only [wp_norm, arm64_norm, hx28_4],
           by simp only [wp_norm, arm64_norm, hsp_4],
           by simp only [wp_norm, arm64_norm, htrace_4],
           by simp only [wp_norm, arm64_norm, hvregs_4]⟩
          (by simp only [wp_norm, arm64_norm, hx19_4])
          (by simp only [wp_norm, arm64_norm, hx20_4])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, add_104_add_48])) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (pin, mk) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

/-- Relocatable `core::ptr::drop_glue::<Vec<session_structure::Chain::MessageKey>>` (Block `3`)
satisfies `withLsCodeLoaded lsmpl (dropVecMessageKeySpecX M A lim)` from `hdealloc`. -/
theorem drop_vec_message_key_placed_ok_of_dealloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H) (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack))) :
    subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (blkPl_3).base
      (withLsCodeLoaded lsmpl (dropVecMessageKeySpecX M A lim)) := by
  have hloop := drop_vec_message_key_placed_loop_ext hdealloc
  unfold withLsCodeLoaded dropVecMessageKeySpecX
  wp_init xst s0
  obtain ⟨⟨v, cap, ptr, mks⟩, st⟩ := xst
  dsimp only
  rw [show dropVecMessageKeyStackX = Proofs.libsignal.Hooks2.dropVecMessageKeyStackX from rfl]
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = v := by assumption
  subst hx0
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropVecMessageKeyX_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop A.repAlloc 104 8 (messageKeyAt A.repAlloc)
      (s0.readReg64 (Reg.gpr 0#5)) cap ptr mks)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine seq_clean_lscl_mk_st hcl0 (mid := (blkPl_3).base + 132#64)
    (P_mid := fun sm =>
      (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 mks.length) ∗
      memRegion ptr (mks.length * 104) ∗
      (if cap = 0 then emp
       else A.repAlloc.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (mks.length * 104)) ((cap.toNat - mks.length) * 104)) ∗
      freePool A lim st sm ∗
      stackAt (s0.sp - 48#64) extHookStack ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = ptr ∧
      sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · cases mks with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
      wp_steps_sync_pool ((blkPl_3).base + 132#64)
      refine SepWP.weaken_pre (sepConj_mono_left (freePool_intro A lim st _)) ?_
      wp_done
    | cons hd tl =>
      have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
      refine seq_clean_lscl_mk_st hcl0 (mid := (blkPl_3).base + 48#64)
        (P_mid := fun sm =>
          arrayAt (messageKeyAt A.repAlloc) 104 ptr (hd :: tl) ∗
          freePool A lim st sm ∗ stackAt (s0.sp - 48#64) extHookStack ∗
          ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
            (if cap = 0 then emp
             else A.repAlloc.live ptr (cap.toNat * 104) 8 ∗
               memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 104)) ((cap.toNat - (hd :: tl).length) * 104)) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm =>
          Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5) ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (hd :: tl).length ∧
          sm.readReg64 .x22 = ptr + 48#64)
        ?_ ?_
      · wp_steps_sync_pool ((blkPl_3).base + 48#64)
        refine SepWP.weaken_pre (sepConj_mono_left (freePool_intro A lim st _)) ?_
        refine align_pre_st (by
          dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
          sep_ac_rfl) ?_
        wp_done
      · intro sm hpcm hrunm hcl_loop ⟨hpresm, hx19m, hx20m, hx21m, hx22m⟩
        refine SepWP.mono
          (hloop s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) ptr hfsp_align st (hd :: tl) ptr sm _
            (List.cons_ne_nil _ _) hlen_lt hpcm hrunm hcl_loop
            hpresm hx19m hx20m hx21m hx22m) ?_
        intro sf Pf _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        exact Entails.of_eq (by sep_ac_rfl)
  · intro sm hpcm hrunm hcl_m ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hx19, hx20⟩
    refine SepWP.weaken_pre
      (post_loop_weaken A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) cap ptr mks.length hlen_le hcap_lt _) ?_
    by_cases hcap : (cap == 0#64) = true
    · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      have hPull :
          (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 16#64) 8 ∗
            freePool A lim st sm ∗
            stackAt (s0.sp - 48#64) extHookStack ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) =
          ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 16#64) 8) ∗
            freePool A lim st sm ∗
            (stackAt (s0.sp - 48#64) extHookStack ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) := by
        sep_ac_rfl
      rw [hPull]
      refine sepWP_elim_freePool fun evs hevs => ?_
      wp_steps_sync_pool (s0.readReg64 .lr)
      refine SepWP.weaken_pre (weaken_pool_to_freePool_front hevs) ?_
      refine SepWP.align_pre_gen
        (P' := (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 16#64) 8 ∗
          freePool A lim st _ ∗
          stackAt (s0.sp - 48#64) extHookStack ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        (by sep_ac_rfl) ?_
      refine SepWP.weaken_pre
        (cap0_weaken_48_extHook (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ s0.sp _ _ _ _ _ _) ?_
      dsimp only [freePool]
      wp_done
    · simp only [Bool.eq_false_iff.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      have hcap_ne : cap ≠ 0 := by
        intro hc; rw [hc] at hcap; revert hcap; decide
      have h0 : cap.toNat ≠ 0 := by
        intro h; apply hcap_ne; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
      have hlayout : RustLayoutOk (cap.toNat * 104) 8 := ⟨layoutOk_mul104_x h0 hcap_lt, by decide⟩
      have hPull :
          (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 16#64) 8 ∗
            (A.repAlloc.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104)) ∗
            freePool A lim st sm ∗
            stackAt (s0.sp - 48#64) extHookStack ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) =
          ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 16#64) 8 ∗
            (A.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104))) ∗
            freePool A lim st sm ∗
            (stackAt (s0.sp - 48#64) extHookStack ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) := by
        have : A.repAlloc.live = A.live := rfl
        rw [this]
        sep_ac_rfl
      rw [hPull]
      refine sepWP_elim_freePool fun evs hevs => ?_
      apply sepWP_seq_lscl hcl_m (mid := lsρ lsRustDeallocSym)
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcl_tail
      have hdealloc_w : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H) (lsρ lsRustDeallocSym)
          (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)) := hdealloc
      have hdealloc0 := lscall_of_withLsCl hdealloc_w hcl_tail
      have hmul : 104#64 * cap = BitVec.ofNat 64 (cap.toNat * 104) := by bv_omega
      refine SepWP.align_pre_gen
        (P' := (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 16#64) 8 ∗
          (A.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104)) ∗
          A.pool lim (M.stepEvents evs st) _ ∗
          stackAt (s0.sp - 48#64) extHookStack ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        (by
          have hmulc : 104 * cap.toNat = cap.toNat * 104 := Nat.mul_comm _ _
          try rw [hmulc]
          sep_ac_rfl) ?_
      refine SepWP.weaken_pre
        (tail_dealloc_pre_weaken_ext (s0.readReg64 (Reg.gpr 0#5)) cap ptr
          (A.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104)) _ s0.sp _ _ _ _ _ _) ?_
      have : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
      wp_call hdealloc0 (ptr, cap.toNat * 104, 8, M.stepEvents evs st)
      refine SepWP.weaken_pre
        (sepConj_mono_left (freePool_step_dealloc A lim st hevs (cap.toNat * 104) 8 _)) ?_
      refine SepWP.weaken_pre (tail_dealloc_post_48_extHook (s0.readReg64 (Reg.gpr 0#5)) _ s0.sp) ?_
      dsimp only [freePool]
      wp_done

/-- Relocatable `core::ptr::drop_glue::<Vec<session_structure::Chain::MessageKey>>` (Block `3`)
satisfies `withLsCodeLoaded lsmpl (dropVecMessageKeySpecX M A lim)` under
`AllocContractsPlaced M A lim H`. -/
theorem drop_vec_message_key_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H) :
    subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (blkPl_3).base
      (withLsCodeLoaded lsmpl (dropVecMessageKeySpecX M A lim)) :=
  drop_vec_message_key_placed_ok_of_dealloc
    (hA.dealloc (callerProg := (blkPC_3).rebase (blkPl_3).base H))

theorem drop_vec_message_key_placed_ok_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 3)
      (withLsCl lsmpl (dropVecMessageKeySpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (j := 3) (callerProg := callerProg)
    (drop_vec_message_key_placed_ok_ext hA)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropsMessageKeyExtBudget
