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
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropsChainExt
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropsMessageKeyExtBudget
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.Common

/-!
# Budget-Threaded `drop_glue::<Vec<Chain>>` (Block `2`)

Verifies relocatable `core::ptr::drop_glue::<Vec<session_structure::Chain>>` (Block `2`) against
`dropVecChainSpecX M A lim`, calling `drop_glue::<Vec<MessageKey>>` (Block `3`) and
`__rust_dealloc`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropsChainExtBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ReceiverChain)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl
  lsρ lsRustDeallocSym sepWP_seq_lscl
)
open CryptoVerification.RustHeap (RustAlloc vecAt arrayAt)
open CryptoVerification.LibsignalSessionRepr (VecPin messageKeyAt ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack ls_subroutine_ok_cl_of_callee
)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  blkPC_2 blkPl_2 dropVecMessageKeyStackX dropVecChainStackX DropVecChainGhost
)
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts (
  chainOuterHeadersAt chainOuterHeadersAt_entails_memRegions chain_memRegions_entails_104
  post_loop_weaken vecAt_expose_loop sep_pull_body sep_push_body sep_rejoin_loop
  tail_len_mul_lt ofNat_succ_eq_add_one ofNat_add_one_beq_one_false
  ofNat_beq_zero_false add_104_add_48 cons_len_mul
)
open Proofs.libsignal.Stage1X (lscall_of_withLsCl)
open Proofs.libsignal.Hooks2 (
  stackAt_dropVecChainX_split stackAt_dropVecMessageKeyX_split_bottom
  tail_dealloc_vecChain_pre_weaken_ext vecChain_tail_dealloc_post_ext
  cap0_weaken_48_vecChain_ext
  ckDeallocX vecPinDeallocX chainAt_entails_deallocX
  layoutOk_u8_x layoutOk_mul104_x SepWP.align_pre_gen
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk
  rustDeallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliDeallocBudgetExternSpecWithStack)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropVecMessageKeySpecX dropVecChainSpecX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropsMessageKeyExtBudget (
  freePool freePool_intro freePool_of_evs freePool_step_dealloc freePool_step_sub
  seq_clean_lscl_mk_st sepWP_elim_freePool drop_vec_message_key_placed_ok_cl
)

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero

/-! ## Block `2` helpers -/

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

private theorem align_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  heq ▸ h

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

private theorem expose_pin_deallocX_zero_ch {A : RustAlloc} {pin : VecPin}
    (hcap : (pin.cap == 0#64) = true) :
    vecPinDeallocX A pin = emp := by
  unfold vecPinDeallocX; simp [hcap]

private theorem expose_pin_deallocX_ch {A : RustAlloc} {pin : VecPin}
    (hcap : ¬ (pin.cap == 0#64) = true) :
    vecPinDeallocX A pin =
      ⌜pin.cap.toNat < 2 ^ 63⌝ ∗ (A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat) := by
  unfold vecPinDeallocX; simp [hcap]

private theorem expose_ckDeallocX_zero {A : RustAlloc} {ckCap ckPtr : BitVec 64}
    (hcap : ckCap.slt 1#64 = true) :
    ckDeallocX A ckCap ckPtr = emp := by
  unfold ckDeallocX; simp [hcap]

private theorem expose_ckDeallocX_ne {A : RustAlloc} {ckCap ckPtr : BitVec 64}
    (hcap : ¬ ckCap.slt 1#64 = true) :
    ckDeallocX A ckCap ckPtr =
      ⌜ckCap.toNat < 2 ^ 63⌝ ∗ (A.live ckPtr ckCap.toNat 1 ∗ memRegion ckPtr ckCap.toNat) := by
  unfold ckDeallocX; simp [hcap]

private theorem pull_ch_pure3 {φ : Prop} {H P R2 : SepProp} :
    (H ∗ (⌜φ⌝ ∗ P)) ∗ R2 = ⌜φ⌝ ∗ ((H ∗ P) ∗ R2) := by
  sep_ac_rfl

private theorem rustLayoutOk_u8_of_ne_zero_ch {cap : BitVec 64}
    (hcap : ¬ (cap == 0#64) = true) (hlt : cap.toNat < 2 ^ 63) :
    RustLayoutOk cap.toNat 1 := by
  refine ⟨layoutOk_u8_x ?_ hlt, by decide⟩
  intro h0
  apply hcap
  have heq : cap = 0#64 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  subst heq; rfl

private theorem rustLayoutOk_u8_of_not_slt1 {ckCap : BitVec 64}
    (hcap : ¬ ckCap.slt 1#64 = true) (hlt : ckCap.toNat < 2 ^ 63) :
    RustLayoutOk ckCap.toNat 1 := by
  refine ⟨layoutOk_u8_x ?_ hlt, by decide⟩
  intro h0
  have heq : ckCap = 0#64 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  rw [heq] at hcap
  exact hcap (by decide)

/-! ## Block `2` body, loop, and entry verification -/

private theorem drop_vec_chain_placed_body_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H) (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)))
    (hdrop_mk : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H) (lsmpl.base 3)
      (withLsCl lsmpl (dropVecMessageKeySpecX M A lim)))
    (s0 : State) (fsp v ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (st : M.σ) :
    ∀ (cur cnt : BitVec 64) (g : ChainGhost) (c : ReceiverChain) (s : State) (Frame : SepProp),
      s.pc = (blkPl_2).base + 56#64 → s.status = .Running → LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp → s.readReg64 .x19 = ptr → s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 → s.readReg64 .x22 = cnt →
      SepWP ((blkPC_2).rebase (blkPl_2).base H) ((blkPl_2).base + 44#64) s
        (chainAt A.repAlloc (g, c) cur ∗ freePool A lim st s ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗ freePool A lim st sm ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
  intro cur cnt g c s Frame hpc hrun hcl hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (chainAt_entails_deallocX A.repAlloc cur g c)) ?_
  wp_pull_exists
  rename_i ckCap ckPtr
  conv =>
    arg 4
    rw [show dropVecMessageKeyStackX = Proofs.libsignal.Hooks2.dropVecMessageKeyStackX from rfl]
    rw [stackAt_dropVecMessageKeyX_split_bottom fsp]
  refine seq_clean_lscl_mk_st hcl (mid := (blkPl_2).base + 76#64)
    (P_mid := fun sm =>
      (chainOuterHeadersAt cur g ckCap ckPtr ∗
        vecPinDeallocX A.repAlloc ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDeallocX A.repAlloc ckCap ckPtr) ∗
      freePool A lim st sm ∗ stackAt fsp extHookStack ∗
      (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr
        (g.keys.zip c.messageKeys) ∗
        memRegion (fsp - 16432#64) 48 ∗ Frame))
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) ?_ ?_
  · refine SepWP.align_pre_gen
      (P' := (cur ↦₆₄ g.srk.cap ∗ (cur + 8#64) ↦₆₄ g.srk.ptr ∗ memRegion (cur + 16#64) 8 ∗
        (cur + 24#64) ↦₆₄ g.priv.cap ∗ (cur + 32#64) ↦₆₄ g.priv.ptr ∗ memRegion (cur + 40#64) 8 ∗
        (cur + 72#64) ↦₆₄ ckCap ∗ (cur + 80#64) ↦₆₄ ckPtr ∗ memRegion (cur + 88#64) 16 ∗
        vecPinDeallocX A.repAlloc ⟨g.srk.cap, g.srk.ptr⟩ ∗
        vecPinDeallocX A.repAlloc ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDeallocX A.repAlloc ckCap ckPtr ∗
        vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys)) ∗
        freePool A lim st s ∗
        (memRegion (fsp - 16432#64) 48 ∗ stackAt fsp extHookStack ∗ Frame))
      (by sep_ac_rfl) ?_
    refine sepWP_elim_freePool fun evs hevs => ?_
    by_cases hcap : (g.srk.cap == 0#64) = true
    · conv => arg 4; rw [expose_pin_deallocX_zero_ch (pin := ⟨g.srk.cap, g.srk.ptr⟩) hcap, emp_sepConj]
      wp_steps_sync_pool ((blkPl_2).base + 76#64)
      refine SepWP.weaken_pre (weaken_pool_to_freePool_front hevs) ?_
      refine align_pre_st (by dsimp only [chainOuterHeadersAt]; sep_ac_rfl) ?_
      wp_done
    · conv => arg 4; rw [expose_pin_deallocX_ch (pin := ⟨g.srk.cap, g.srk.ptr⟩) hcap]; simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hlayout := rustLayoutOk_u8_of_ne_zero_ch hcap hcap_lt
      apply sepWP_seq_lscl hcl (mid := lsρ lsRustDeallocSym)
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
      have hdealloc_w : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H) (lsρ lsRustDeallocSym)
          (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)) := hdealloc
      have hcall := lscall_of_withLsCl hdealloc_w hcl_c
      have : A.repAlloc.live = A.live := rfl
      rw [this]
      have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      wp_call hcall (g.srk.ptr, g.srk.cap.toNat, 1, M.stepEvents evs st)
      refine SepWP.weaken_pre (weaken_dealloc_to_freePool_front hevs) ?_
      refine align_pre_st (by dsimp only [chainOuterHeadersAt]; rw [hsp]; sep_ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
    refine seq_clean_lscl_mk_st hcl1 (mid := (blkPl_2).base + 96#64)
      (P_mid := fun sm =>
        (chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDeallocX A.repAlloc ckCap ckPtr) ∗
        freePool A lim st sm ∗ stackAt fsp extHookStack ∗
        (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) ∗
          memRegion (fsp - 16432#64) 48 ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) ?_ ?_
    · refine sepWP_elim_freePool fun evs hevs => ?_
      by_cases hcap : (g.priv.cap == 0#64) = true
      · conv => arg 4; rw [expose_pin_deallocX_zero_ch (pin := ⟨g.priv.cap, g.priv.ptr⟩) hcap, emp_sepConj]; dsimp only [chainOuterHeadersAt]
        wp_steps_sync_pool ((blkPl_2).base + 96#64)
        refine SepWP.weaken_pre (weaken_pool_to_freePool_front hevs) ?_
        refine align_pre_st (by dsimp only [chainOuterHeadersAt]; sep_ac_rfl) ?_
        wp_done
      · conv => arg 4; rw [expose_pin_deallocX_ch (pin := ⟨g.priv.cap, g.priv.ptr⟩) hcap]; dsimp only [chainOuterHeadersAt]; simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
        refine SepWP.pure_elim fun hcap_lt => ?_
        have hlayout := rustLayoutOk_u8_of_ne_zero_ch hcap hcap_lt
        apply sepWP_seq_lscl hcl1 (mid := lsρ lsRustDeallocSym)
        wp_steps_sync_pool (lsρ lsRustDeallocSym)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
        have hdealloc_w : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H) (lsρ lsRustDeallocSym)
            (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)) := hdealloc
        have hcall := lscall_of_withLsCl hdealloc_w hcl_c
        have : A.repAlloc.live = A.live := rfl
        rw [this]
        have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
        wp_call hcall (g.priv.ptr, g.priv.cap.toNat, 1, M.stepEvents evs st)
        refine SepWP.weaken_pre (weaken_dealloc_to_freePool_front hevs) ?_
        refine align_pre_st (by dsimp only [chainOuterHeadersAt]; rw [hsp_1]; sep_ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine seq_clean_lscl_mk_st hcl2 (mid := (blkPl_2).base + 36#64)
        (P_mid := fun sm =>
          vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr
            (g.keys.zip c.messageKeys) ∗
          freePool A lim st sm ∗ stackAt fsp dropVecMessageKeyStackX ∗
          ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) ?_ ?_
      · have hstep3 : SepWP ((blkPC_2).rebase (blkPl_2).base H)
            ((blkPl_2).base + 36#64) s2
            ((chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDeallocX A.repAlloc ckCap ckPtr) ∗
              freePool A lim st s2 ∗ stackAt fsp extHookStack ∗
              (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr
                (g.keys.zip c.messageKeys) ∗
                memRegion (fsp - 16432#64) 48 ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ chainOuterHeadersAt cur g ckCap ckPtr ∗
                freePool A lim st sm ∗ stackAt fsp extHookStack ∗
                (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr
                  (g.keys.zip c.messageKeys) ∗
                  memRegion (fsp - 16432#64) 48 ∗ Frame)) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          refine sepWP_elim_freePool fun evs hevs => ?_
          by_cases hcap : ckCap.slt 1#64 = true
          · conv => arg 4; rw [expose_ckDeallocX_zero hcap, sepConj_emp]; dsimp only [chainOuterHeadersAt]
            wp_steps_sync_pool ((blkPl_2).base + 36#64)
            refine SepWP.weaken_pre (weaken_pool_to_freePool_front hevs) ?_
            refine align_pre_st (by dsimp only [chainOuterHeadersAt]; sep_ac_rfl) ?_
            wp_done
          · conv => arg 4; rw [expose_ckDeallocX_ne hcap, pull_ch_pure3]; dsimp only [chainOuterHeadersAt]
            refine SepWP.pure_elim fun hcap_lt => ?_
            have hlayout := rustLayoutOk_u8_of_not_slt1 hcap hcap_lt
            apply sepWP_seq_lscl hcl2 (mid := lsρ lsRustDeallocSym)
            wp_steps_sync_pool (lsρ lsRustDeallocSym)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
            have hdealloc_w : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H) (lsρ lsRustDeallocSym)
                (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)) := hdealloc
            have hcall := lscall_of_withLsCl hdealloc_w hcl_c
            have : A.repAlloc.live = A.live := rfl
            rw [this]
            have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
            wp_call hcall (ckPtr, ckCap.toNat, 1, M.stepEvents evs st)
            wp_steps_sync_pool ((blkPl_2).base + 36#64)
            refine SepWP.weaken_pre
              (sepConj_mono_left (freePool_step_dealloc A lim st hevs ckCap.toNat 1 _)) ?_
            refine align_pre_st (by dsimp only [chainOuterHeadersAt]; rw [hsp_2]; sep_ac_rfl) ?_
            wp_done
        refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
        refine Entails.trans (sepConj_mono_left (chainOuterHeadersAt_entails_memRegions cur g ckCap ckPtr)) ?_
        rw [show dropVecMessageKeyStackX = Proofs.libsignal.Hooks2.dropVecMessageKeyStackX from rfl]
        rw [stackAt_dropVecMessageKeyX_split_bottom fsp]
        exact Entails.of_eq (by sep_ac_rfl)
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        have hstep4 : SepWP ((blkPC_2).rebase (blkPl_2).base H)
            ((blkPl_2).base + 44#64) s3
            (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr
              (g.keys.zip c.messageKeys) ∗
              freePool A lim st s3 ∗ stackAt fsp dropVecMessageKeyStackX ∗
              ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ (memRegion (cur + 48#64) 24 ∗ memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗
                freePool A lim st sm ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          refine sepWP_elim_freePool fun evs hevs => ?_
          apply sepWP_seq_lscl hcl3 (mid := lsmpl.base 3)
          wp_steps_sync_pool (lsmpl.base 3)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro hcl_mk
          have hdrop_mk_w : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H) (lsmpl.base 3)
              (withLsCl lsmpl (dropVecMessageKeySpecX M A lim)) := hdrop_mk
          have hcall_mk := lscall_of_withLsCl hdrop_mk_w hcl_mk
          wp_call hcall_mk (⟨cur + 48#64, g.mkCap, g.mkPtr, g.keys.zip c.messageKeys⟩, M.stepEvents evs st)
          refine SepWP.align_pre_gen
            (P' := A.pool lim (M.stepEvents _ (M.stepEvents evs st)) _ ∗
              ((memRegion (cur + 48#64) 24 ∗ memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗
                stackAt fsp dropVecMessageKeyStackX ∗ Frame))
            (by rw [hsp_3]; sep_ac_rfl) ?_
          refine SepWP.weaken_pre (sepConj_mono_left
            (Entails.trans
              (freePool_of_evs A lim (M.stepEvents evs st) (by assumption) _)
              (freePool_step_sub A lim st hevs _))) ?_
          refine align_pre_st (by sep_ac_rfl) ?_
          wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (chain_memRegions_entails_104 cur)), h.2⟩)

private theorem drop_vec_chain_placed_loop_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H) (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)))
    (hdrop_mk : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H) (lsmpl.base 3)
      (withLsCl lsmpl (dropVecMessageKeySpecX M A lim)))
    (s0 : State) (fsp v ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (st : M.σ) :
    ∀ (rest : List (ChainGhost × ReceiverChain)) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 104 < 2 ^ 63 →
      s.pc = (blkPl_2).base + 56#64 → s.status = .Running → LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp → s.readReg64 .x19 = ptr → s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 → s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      SepWP ((blkPC_2).rebase (blkPl_2).base H) ((blkPl_2).base + 124#64) s
        (arrayAt (chainAt A.repAlloc) 104 cur rest ∗ freePool A lim st s ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ freePool A lim st sm ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v) := by
  have hbody := drop_vec_chain_placed_body_ext hdealloc hdrop_mk s0 fsp v ptr hfsp_align st
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨g, c⟩
    intro cur s Frame _ hlen hpc hrun hcl hpres hx19 hx20 hx21 hx22
    rw [show arrayAt (chainAt A.repAlloc) 104 cur ((g, c) :: tl) =
          chainAt A.repAlloc (g, c) cur ∗ arrayAt (chainAt A.repAlloc) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine seq_clean_lscl_mk_st hcl (mid := (blkPl_2).base + 44#64)
      (hbody cur (BitVec.ofNat 64 ((g, c) :: tl).length) g c s
        (arrayAt (chainAt A.repAlloc) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hcl hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 hcl4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4, hx21_4, hx22_4⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx22_4 ⊢
      refine sepWP_elim_freePool fun evs hevs => ?_
      wp_steps_sync_pool ((blkPl_2).base + 124#64)
      refine SepWP.weaken_pre (weaken_pool_to_freePool_front hevs) ?_
      wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show ((g, c) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx22_4
      have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
      refine sepWP_elim_freePool fun evs hevs => ?_
      apply sepWP_seq_lscl hcl4 (mid := (blkPl_2).base + 56#64)
      wp_steps_sync_pool ((blkPl_2).base + 56#64)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcl5
      refine SepWP.weaken_pre (weaken_pool_to_freePool_front hevs) ?_
      refine SepWP.align_pre_gen
        (P' := arrayAt (chainAt A.repAlloc) 104 (cur + 104#64) (hd2 :: tl2) ∗
          freePool A lim st _ ∗ stackAt fsp dropVecMessageKeyStackX ∗ (memRegion cur 104 ∗ Frame))
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
          (by simp only [wp_norm, arm64_norm, add_104_add_48])
          (by simp only [wp_norm, arm64_norm])) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (g, c) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

/-- Relocatable `core::ptr::drop_glue::<Vec<session_structure::Chain>>` (Block `2`) satisfies
`withLsCodeLoaded lsmpl (dropVecChainSpecX M A lim)` from `hdealloc` and `hdrop_mk`. -/
theorem drop_vec_chain_placed_ok_of_callees [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H) (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)))
    (hdrop_mk : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H) (lsmpl.base 3)
      (withLsCl lsmpl (dropVecMessageKeySpecX M A lim))) :
    subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base
      (withLsCodeLoaded lsmpl (dropVecChainSpecX M A lim)) := by
  have hloop := drop_vec_chain_placed_loop_ext hdealloc hdrop_mk
  unfold withLsCodeLoaded dropVecChainSpecX
  wp_init xst s0
  obtain ⟨⟨v, cap, ptr, cs⟩, st⟩ := xst
  dsimp only
  rw [show dropVecChainStackX = Proofs.libsignal.Hooks2.dropVecChainStackX from rfl]
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = v := by assumption
  subst hx0
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropVecChainX_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop A.repAlloc 104 8 (chainAt A.repAlloc)
      (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine seq_clean_lscl_mk_st hcl0 (mid := (blkPl_2).base + 124#64)
    (P_mid := fun sm =>
      (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
      memRegion ptr (cs.length * 104) ∗
      (if cap = 0 then emp
       else A.repAlloc.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) ∗
      freePool A lim st sm ∗
      stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = ptr ∧
      sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · cases cs with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
      wp_steps_sync_pool ((blkPl_2).base + 124#64)
      refine SepWP.weaken_pre (sepConj_mono_left (freePool_intro A lim st _)) ?_
      wp_done
    | cons hd tl =>
      have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
      refine seq_clean_lscl_mk_st hcl0 (mid := (blkPl_2).base + 56#64)
        (P_mid := fun sm =>
          arrayAt (chainAt A.repAlloc) 104 ptr (hd :: tl) ∗
          freePool A lim st sm ∗ stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
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
          sm.readReg64 .x21 = ptr + 48#64 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (hd :: tl).length)
        ?_ ?_
      · wp_steps_sync_pool ((blkPl_2).base + 56#64)
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
      (post_loop_weaken A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs.length hlen_le hcap_lt _) ?_
    by_cases hcap : (cap == 0#64) = true
    · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      have hPull :
          (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 16#64) 8 ∗
            freePool A lim st sm ∗
            stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) =
          ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 16#64) 8) ∗
            freePool A lim st sm ∗
            (stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
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
          stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        (by sep_ac_rfl) ?_
      refine SepWP.weaken_pre
        (cap0_weaken_48_vecChain_ext (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ s0.sp _ _ _ _ _ _) ?_
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
            stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) =
          ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 16#64) 8 ∗
            (A.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104))) ∗
            freePool A lim st sm ∗
            (stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
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
      have hdealloc_w : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H) (lsρ lsRustDeallocSym)
          (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)) := hdealloc
      have hdealloc0 := lscall_of_withLsCl hdealloc_w hcl_tail
      have hmul : 104#64 * cap = BitVec.ofNat 64 (cap.toNat * 104) := by bv_omega
      refine SepWP.align_pre_gen
        (P' := (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 16#64) 8 ∗
          (A.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104)) ∗
          A.pool lim (M.stepEvents evs st) _ ∗
          stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        (by
          have hmulc : 104 * cap.toNat = cap.toNat * 104 := Nat.mul_comm _ _
          try rw [hmulc]
          sep_ac_rfl) ?_
      refine SepWP.weaken_pre
        (tail_dealloc_vecChain_pre_weaken_ext (s0.readReg64 (Reg.gpr 0#5)) cap ptr
          (A.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104)) _ s0.sp _ _ _ _ _ _) ?_
      have : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
      wp_call hdealloc0 (ptr, cap.toNat * 104, 8, M.stepEvents evs st)
      refine SepWP.weaken_pre
        (sepConj_mono_left (freePool_step_dealloc A lim st hevs (cap.toNat * 104) 8 _)) ?_
      refine SepWP.weaken_pre
        (vecChain_tail_dealloc_post_ext (s0.readReg64 (Reg.gpr 0#5)) _ s0.sp) ?_
      dsimp only [freePool]
      wp_done

/-- Relocatable `core::ptr::drop_glue::<Vec<session_structure::Chain>>` (Block `2`) satisfies
`withLsCodeLoaded lsmpl (dropVecChainSpecX M A lim)` under `AllocContractsPlaced M A lim H`. -/
theorem drop_vec_chain_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H) :
    subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base
      (withLsCodeLoaded lsmpl (dropVecChainSpecX M A lim)) :=
  drop_vec_chain_placed_ok_of_callees
    (hA.dealloc (callerProg := (blkPC_2).rebase (blkPl_2).base H))
    (drop_vec_message_key_placed_ok_cl
      (callerProg := (blkPC_2).rebase (blkPl_2).base H) hA)

theorem drop_vec_chain_placed_ok_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 2)
      (withLsCl lsmpl (dropVecChainSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (drop_vec_chain_placed_ok_ext hA)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropsChainExtBudget
