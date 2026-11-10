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
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1Ext
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropsChainExtBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Budget-Threaded `drop_glue::<SessionStructure> [local#1]` (Block `6`)

Verifies relocatable `core::ptr::drop_glue::<SessionStructure> [local#1]` (Block `6`) against
`dropSessionStructureLocal1SpecX M A lim` over `FreeOnlyEvs`-evolved `RustCliAllocBudget` pools,
calling `drop_glue::<Vec<MessageKey>>` (Block `3`), `drop_glue::<Vec<Chain>>` (Block `2`), and
`__rust_dealloc`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1ExtBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (SenderChain)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl
  blkPC_6 blkPl_6 lsρ lsRustDeallocSym sepWP_seq_lscl
)
open CryptoVerification.RustHeap (RustAlloc vecAt)
open CryptoVerification.LibsignalSessionRepr (VecPin messageKeyAt chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SenderChainGhost SessionGhost noneCap optSenderChainAt
)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack ls_subroutine_ok_cl_of_callee
)
open Proofs.libsignal.Stage1X (lscall_of_withLsCl)
open Proofs.libsignal.Hooks2 (
  dropSessionStructureLocal1StackX dropVecChainStackX dropVecMessageKeyStackX
  Saved32Preserved ssPresQ
  stackAt_ss_local1_split_x stackAt_dropVecChainX_split_alloc stackAt_dropVecChainX_split_mk
  stackAt_dropVecMessageKeyX_split_alloc tail_stack_128_from_bottom_ext
  tail_dealloc_ss_local1_pre_weaken_ext
  ssFirst3HeadersAt ssFirst3HeadersAt_entails_memRegions_x
  ssTail3HeadersAt ssTail3HeadersAt_entails_memRegions_x
  sessionStateAt_entails_dealloc_x
  ssSender1HeadersAt ssSender1HeadersAt_entails_memRegions_x
  optSenderChainAt_some_entails_ss_local1_x
  ssSender1_memRegions_entails_104_x sender_none_entails_memRegion_104_x
  session_memRegions_entails_344_x pq_header24_weaken_x
  hcap_false_elim hslt_false_elim
  ssSavedFrame ssPqPart ssTail3Dealloc ssFirst3Mem ss9MemRegions
  vecPinDeallocX sgnPinDeallocX ckDeallocX
  layoutOk_u8_x SepWP.align_pre_gen SepWP.false_elim_left
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk
  rustDeallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliDeallocBudgetExternSpecWithStack)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.AdaptersBudget (Stage2ContractsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropVecMessageKeySpecX dropVecChainSpecX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropsMessageKeyExtBudget (
  freePool freePool_intro freePool_of_evs freePool_step_dealloc freePool_step_sub
  seq_clean_lscl_mk_st sepWP_elim_freePool drop_vec_message_key_placed_ok_cl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropsChainExtBudget (
  drop_vec_chain_placed_ok_cl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  SerContractsXPlaced serContractsXPlaced_of_stage2ContractsPlaced
  dropSessionStructureLocal1SpecX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  DropSessionStructureLocal1PlacedOkX
)

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Framing and `freePool` helpers -/

private theorem align_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  heq ▸ h

private theorem weaken_pool_to_freePool_2nd {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {s : State} {L R : SepProp} :
    L ∗ A.pool lim (M.stepEvents evs st) s ∗ R ⊢ L ∗ freePool A lim st s ∗ R :=
  sepConj_mono_right (sepConj_mono_left (freePool_of_evs A lim st hevs s))

private theorem weaken_dealloc_to_freePool_2nd {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {sz align : Nat} {s : State} {L R : SepProp} :
    L ∗ A.pool lim (M.stepEvents (rustDeallocEvents sz align) (M.stepEvents evs st)) s ∗ R ⊢
      L ∗ freePool A lim st s ∗ R :=
  sepConj_mono_right (sepConj_mono_left (freePool_step_dealloc A lim st hevs sz align s))

private theorem weaken_sub_to_freePool_2nd {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {evs₁ evs₂ : List AllocEvent}
    (hevs₁ : FreeOnlyEvs evs₁) (hevs₂ : FreeOnlyEvs evs₂)
    {s : State} {L R : SepProp} :
    L ∗ A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s ∗ R ⊢
      L ∗ freePool A lim st s ∗ R :=
  sepConj_mono_right (sepConj_mono_left
    (Entails.trans (freePool_of_evs A lim (M.stepEvents evs₁ st) hevs₂ s)
      (freePool_step_sub A lim st hevs₁ s)))

private theorem expose_pin_zero {A : RustAlloc} {pin : VecPin}
    (hcap : (pin.cap == 0#64) = true) :
    vecPinDeallocX A pin = emp := by
  unfold vecPinDeallocX; simp [hcap]

private theorem expose_pin_ne {A : RustAlloc} {pin : VecPin}
    (hcap : ¬ (pin.cap == 0#64) = true) :
    vecPinDeallocX A pin =
      ⌜pin.cap.toNat < 2 ^ 63⌝ ∗ (A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat) := by
  unfold vecPinDeallocX; simp [hcap]

private theorem expose_sgn_zero {A : RustAlloc} {cap ptr : BitVec 64}
    (hcap : cap.slt 1#64 = true) :
    sgnPinDeallocX A cap ptr = emp := by
  unfold sgnPinDeallocX ckDeallocX; simp [hcap]

private theorem expose_sgn_ne {A : RustAlloc} {cap ptr : BitVec 64}
    (hcap : ¬ cap.slt 1#64 = true) :
    sgnPinDeallocX A cap ptr =
      ⌜cap.toNat < 2 ^ 63⌝ ∗ (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold sgnPinDeallocX ckDeallocX; simp [hcap]

private theorem rustLayoutOk_u8_of_ne_zero {cap : BitVec 64}
    (hcap : ¬ (cap == 0#64) = true) (hlt : cap.toNat < 2 ^ 63) :
    RustLayoutOk cap.toNat 1 :=
  ⟨layoutOk_u8_x (fun hc => hcap_false_elim (eq_false hcap) hc) hlt, by decide⟩

private theorem rustLayoutOk_u8_of_not_slt1 {cap : BitVec 64}
    (hcap : ¬ cap.slt 1#64 = true) (hlt : cap.toNat < 2 ^ 63) :
    RustLayoutOk cap.toNat 1 :=
  ⟨layoutOk_u8_x (fun hc => hslt_false_elim (eq_false hcap) hc) hlt, by decide⟩

private theorem ss_epilogue_mem344 (ss : BitVec 64) :
    memRegion (ss + 120#64) 24 ∗ ss9MemRegions ss ⊢ memRegion ss 344 := by
  refine Entails.trans ?_ (session_memRegions_entails_344_x ss)
  dsimp only [ss9MemRegions]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem stack_128_extHook_eq_ss_local1 (sp : BitVec 64) :
    memRegion (sp - 16512#64) 128 ∗ stackAt sp extHookStack =
      stackAt sp dropSessionStructureLocal1StackX := by
  have hsplit := ProofLib.stackAt_split_bottom sp extHookStack 128 (by decide)
  have hext : sp - BitVec.ofNat 64 (extHookStack + 128) = sp - 16512#64 := rfl
  rw [hext] at hsplit
  rw [← hsplit]
  rfl

private theorem ss_epilogue_cap0_weaken {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    (ss cap ptr : BitVec 64) (sp fp lr x19 v3 : BitVec 64) (sf : State) :
    (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗ emp) ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      (ss9MemRegions ss ∗ stackAt (sp - 32#64) dropVecChainStackX ∗
        (((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3))) ⊢
    memRegion ss 344 ∗ freePool A lim st sf ∗ stackAt sp dropSessionStructureLocal1StackX := by
  have hmem :
      ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗
        memRegion (ss + 136#64) 8 ∗ ss9MemRegions ss ⊢
      memRegion ss 344 :=
    Entails.trans (pq_header24_weaken_x ss cap ptr (ss9MemRegions ss)) (ss_epilogue_mem344 ss)
  have hstk :
      stackAt (sp - 32#64) dropVecChainStackX ∗
        (((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3)) ⊢
      stackAt sp dropSessionStructureLocal1StackX := by
    rw [← stack_128_extHook_eq_ss_local1 sp, tail_stack_128_from_bottom_ext sp]
    cells_unfold
    exact Entails.sepExists_right fp (Entails.sepExists_right lr
      (Entails.sepExists_right x19 (Entails.sepExists_right v3 (Entails.refl _))))
  have hreord :
      ((((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗ emp) ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        (ss9MemRegions ss ∗ stackAt (sp - 32#64) dropVecChainStackX ∗
          (((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
            ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3)))) =
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗
        memRegion (ss + 136#64) 8 ∗ ss9MemRegions ss) ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      (stackAt (sp - 32#64) dropVecChainStackX ∗
        (((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3))) := by
    simp only [sepConj_emp]
    sep_ac_rfl
  rw [hreord]
  exact sepConj_mono hmem (sepConj_mono (freePool_of_evs A lim st hevs sf) hstk)

private theorem ss_epilogue_dealloc_post_weaken {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    (ss : BitVec 64) (sz : Nat) (sp : BitVec 64) (sf : State) :
    (memRegion (ss + 120#64) 24 ∗ ss9MemRegions ss) ∗
      A.pool lim (M.stepEvents (rustDeallocEvents sz 1) (M.stepEvents evs st)) sf ∗
      (memRegion (sp - 16512#64) 128 ∗ stackAt sp extHookStack) ⊢
    memRegion ss 344 ∗ freePool A lim st sf ∗ stackAt sp dropSessionStructureLocal1StackX := by
  rw [stack_128_extHook_eq_ss_local1 sp]
  exact sepConj_mono (ss_epilogue_mem344 ss)
    (sepConj_mono_left (freePool_step_dealloc A lim st hevs sz 1 sf))

/-! ## Block `6` segment lemmas -/

private theorem drop_ss_local1_placed_first3_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (st : M.σ) :
    ∀ (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (blkPl_6).base + 12#64 →
      s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved32Preserved s0 s fsp →
      s.readReg64 .x0 = ss →
      SepWP ((blkPC_6).rebase (blkPl_6).base H)
        ((blkPl_6).base + 76#64)
        s
        ((ssFirst3HeadersAt ss G ∗
          vecPinDeallocX A.repAlloc ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDeallocX A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDeallocX A.repAlloc G.root) ∗
          freePool A lim st s ∗ stackAt fsp extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24) ∗
            freePool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  intro G s Frame hpc hrun hcl hpres hx0
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine seq_clean_lscl_mk_st hcl (mid := (blkPl_6).base + 36#64)
    (P_mid := fun sm =>
      (ssFirst3HeadersAt ss G ∗
        vecPinDeallocX A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDeallocX A.repAlloc G.root) ∗
      freePool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame)
    (Q := ssPresQ s0 fsp ss) ?_ ?_
  · refine sepWP_elim_freePool fun evs hevs => ?_
    by_cases hcap : (G.localIk.cap == 0#64) = true
    · conv => arg 4; rw [expose_pin_zero (pin := ⟨G.localIk.cap, G.localIk.ptr⟩) hcap]
      dsimp only [ssFirst3HeadersAt]
      wp_steps_sync_pool ((blkPl_6).base + 36#64)
      refine SepWP.align_pre_gen
        (P' := (ssFirst3HeadersAt ss G ∗
          vecPinDeallocX A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDeallocX A.repAlloc G.root) ∗
          A.pool lim (M.stepEvents evs st) _ ∗ (stackAt fsp extHookStack ∗ Frame))
        (by dsimp only [ssFirst3HeadersAt]; sep_ac_rfl) ?_
      refine SepWP.weaken_pre (weaken_pool_to_freePool_2nd hevs) ?_
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · conv => arg 4; rw [expose_pin_ne (pin := ⟨G.localIk.cap, G.localIk.ptr⟩) hcap]
      dsimp only [ssFirst3HeadersAt]
      simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hlayout := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
      apply sepWP_seq_lscl hcl (mid := lsρ lsRustDeallocSym)
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
      have hcall := lscall_of_withLsCl hdealloc hcl_c
      have hlive : A.repAlloc.live = A.live := rfl
      rw [hlive]
      have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      wp_call hcall (G.localIk.ptr, G.localIk.cap.toNat, 1, M.stepEvents evs st)
      refine SepWP.align_pre_gen
        (P' := (ssFirst3HeadersAt ss G ∗
          vecPinDeallocX A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDeallocX A.repAlloc G.root) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents G.localIk.cap.toNat 1) (M.stepEvents evs st)) _ ∗
          (stackAt fsp extHookStack ∗ Frame))
        (by dsimp only [ssFirst3HeadersAt]; rw [hsp]; sep_ac_rfl) ?_
      refine SepWP.weaken_pre (weaken_dealloc_to_freePool_2nd hevs) ?_
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean_lscl_mk_st hcl1 (mid := (blkPl_6).base + 56#64)
      (P_mid := fun sm =>
        (ssFirst3HeadersAt ss G ∗ vecPinDeallocX A.repAlloc G.root) ∗
        freePool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame)
      (Q := ssPresQ s0 fsp ss) ?_ ?_
    · refine sepWP_elim_freePool fun evs hevs => ?_
      by_cases hcap : (G.remoteIk.cap == 0#64) = true
      · conv => arg 4; rw [expose_pin_zero (pin := ⟨G.remoteIk.cap, G.remoteIk.ptr⟩) hcap]
        dsimp only [ssFirst3HeadersAt]
        wp_steps_sync_pool ((blkPl_6).base + 56#64)
        refine SepWP.align_pre_gen
          (P' := (ssFirst3HeadersAt ss G ∗ vecPinDeallocX A.repAlloc G.root) ∗
            A.pool lim (M.stepEvents evs st) _ ∗ (stackAt fsp extHookStack ∗ Frame))
          (by dsimp only [ssFirst3HeadersAt]; sep_ac_rfl) ?_
        refine SepWP.weaken_pre (weaken_pool_to_freePool_2nd hevs) ?_
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · conv => arg 4; rw [expose_pin_ne (pin := ⟨G.remoteIk.cap, G.remoteIk.ptr⟩) hcap]
        dsimp only [ssFirst3HeadersAt]
        simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
        refine SepWP.pure_elim fun hcap_lt => ?_
        have hlayout := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
        apply sepWP_seq_lscl hcl1 (mid := lsρ lsRustDeallocSym)
        wp_steps_sync_pool (lsρ lsRustDeallocSym)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
        have hcall := lscall_of_withLsCl hdealloc hcl_c
        have hlive : A.repAlloc.live = A.live := rfl
        rw [hlive]
        have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
        wp_call hcall (G.remoteIk.ptr, G.remoteIk.cap.toNat, 1, M.stepEvents evs st)
        refine SepWP.align_pre_gen
          (P' := (ssFirst3HeadersAt ss G ∗ vecPinDeallocX A.repAlloc G.root) ∗
            A.pool lim (M.stepEvents (rustDeallocEvents G.remoteIk.cap.toNat 1) (M.stepEvents evs st)) _ ∗
            (stackAt fsp extHookStack ∗ Frame))
          (by dsimp only [ssFirst3HeadersAt]; rw [hsp_1]; sep_ac_rfl) ?_
        refine SepWP.weaken_pre (weaken_dealloc_to_freePool_2nd hevs) ?_
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 76#64) s2
          ((ssFirst3HeadersAt ss G ∗ vecPinDeallocX A.repAlloc G.root) ∗
            freePool A lim st s2 ∗ stackAt fsp extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssFirst3HeadersAt ss G ∗ freePool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
        refine sepWP_elim_freePool fun evs hevs => ?_
        by_cases hcap : (G.root.cap == 0#64) = true
        · conv => arg 4; rw [expose_pin_zero (pin := G.root) hcap]
          dsimp only [ssFirst3HeadersAt]
          wp_steps_sync_pool ((blkPl_6).base + 76#64)
          refine SepWP.align_pre_gen
            (P' := ssFirst3HeadersAt ss G ∗
              A.pool lim (M.stepEvents evs st) _ ∗ (stackAt fsp extHookStack ∗ Frame))
            (by dsimp only [ssFirst3HeadersAt]; sep_ac_rfl) ?_
          refine SepWP.weaken_pre (weaken_pool_to_freePool_2nd hevs) ?_
          refine align_pre_st (by sep_ac_rfl) ?_
          wp_done
        · conv => arg 4; rw [expose_pin_ne (pin := G.root) hcap]
          dsimp only [ssFirst3HeadersAt]
          simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
          refine SepWP.pure_elim fun hcap_lt => ?_
          have hlayout := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
          apply sepWP_seq_lscl hcl2 (mid := lsρ lsRustDeallocSym)
          wp_steps_sync_pool (lsρ lsRustDeallocSym)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
          have hcall := lscall_of_withLsCl hdealloc hcl_c
          have hlive : A.repAlloc.live = A.live := rfl
          rw [hlive]
          have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
          wp_call hcall (G.root.ptr, G.root.cap.toNat, 1, M.stepEvents evs st)
          refine SepWP.align_pre_gen
            (P' := ssFirst3HeadersAt ss G ∗
              A.pool lim (M.stepEvents (rustDeallocEvents G.root.cap.toNat 1) (M.stepEvents evs st)) _ ∗
              (stackAt fsp extHookStack ∗ Frame))
            (by dsimp only [ssFirst3HeadersAt]; rw [hsp_2]; sep_ac_rfl) ?_
          refine SepWP.weaken_pre (weaken_dealloc_to_freePool_2nd hevs) ?_
          refine align_pre_st (by sep_ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssFirst3HeadersAt_entails_memRegions_x ss G)), h.2⟩)

private theorem drop_ss_local1_placed_sender_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)))
    (hdrop_mk : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (lsmpl.base 3)
      (withLsCl lsmpl (dropVecMessageKeySpecX M A lim)))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (st : M.σ) :
    ∀ (senderG : Option SenderChainGhost) (senderSt : Option SenderChain)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_6).base + 76#64 →
      s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved32Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP ((blkPC_6).rebase (blkPl_6).base H)
        ((blkPl_6).base + 156#64)
        s
        (optSenderChainAt A.repAlloc (ss + 144#64) senderG senderSt ∗
          freePool A lim st s ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 144#64) 104 ∗ freePool A lim st sm ∗
            stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  intro senderG senderSt s Frame hpc hrun hcl hpres hx19
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  cases senderG with
  | none =>
    cases senderSt with
    | none =>
      have hnone : optSenderChainAt A.repAlloc (ss + 144#64) none none =
          (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) := by
        unfold optSenderChainAt; rw [show (ss + 144#64) + 8#64 = ss + 152#64 by bv_omega]
      rw [hnone]
      have hstep : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 156#64) s
          ((((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) ∗
            freePool A lim st s ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) ∗
              freePool A lim st sm ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
        refine sepWP_elim_freePool fun evs hevs => ?_
        dsimp only [noneCap]
        wp_steps_sync_pool ((blkPl_6).base + 156#64)
        refine SepWP.align_pre_gen
          (P' := (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) ∗
            A.pool lim (M.stepEvents evs st) _ ∗ (stackAt fsp dropVecMessageKeyStackX ∗ Frame))
          (by dsimp only [noneCap]; sep_ac_rfl) ?_
        refine SepWP.weaken_pre (weaken_pool_to_freePool_2nd hevs) ?_
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      refine SepWP.mono hstep (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
      rw [show ss + 152#64 = (ss + 144#64) + 8#64 by bv_omega]
      exact sepConj_mono_left (sender_none_entails_memRegion_104_x (ss + 144#64))
    | some _ => simp only [optSenderChainAt]; exact SepWP.false_elim_left
  | some sg =>
    cases senderSt with
    | none => simp only [optSenderChainAt]; exact SepWP.false_elim_left
    | some sc =>
      refine SepWP.weaken_pre
        (sepConj_mono_left (optSenderChainAt_some_entails_ss_local1_x A.repAlloc ss sg sc)) ?_
      wp_pull_exists
      rename_i ckCap ckPtr
      refine SepWP.pure_elim fun hcmn => ?_
      have hcmn_beq : (sg.srk.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
      rw [stackAt_dropVecMessageKeyX_split_alloc fsp]
      refine SepWP.weaken_pre (P' :=
        (ssSender1HeadersAt ss sg ckCap ckPtr ∗
          vecPinDeallocX A.repAlloc ⟨sg.srk.cap, sg.srk.ptr⟩ ∗
          vecPinDeallocX A.repAlloc ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDeallocX A.repAlloc ckCap ckPtr) ∗
        freePool A lim st s ∗ stackAt fsp extHookStack ∗
        (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
          memRegion (fsp - 16432#64) 48 ∗ Frame))
        (Entails.of_eq (by dsimp only [ssSender1HeadersAt]; sep_ac_rfl)) ?_
      refine seq_clean_lscl_mk_st hcl (mid := (blkPl_6).base + 104#64)
        (P_mid := fun sm =>
          (ssSender1HeadersAt ss sg ckCap ckPtr ∗
            vecPinDeallocX A.repAlloc ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
            sgnPinDeallocX A.repAlloc ckCap ckPtr) ∗
          freePool A lim st sm ∗ stackAt fsp extHookStack ∗
          (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
            memRegion (fsp - 16432#64) 48 ∗ Frame))
        (Q := ssPresQ s0 fsp ss) ?_ ?_
      · refine sepWP_elim_freePool fun evs hevs => ?_
        by_cases hcap : (sg.srk.cap == 0#64) = true
        · conv => arg 4; rw [expose_pin_zero (pin := ⟨sg.srk.cap, sg.srk.ptr⟩) hcap]
          dsimp only [ssSender1HeadersAt]
          wp_steps_sync_pool ((blkPl_6).base + 104#64)
          refine SepWP.align_pre_gen
            (P' := (ssSender1HeadersAt ss sg ckCap ckPtr ∗
              vecPinDeallocX A.repAlloc ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
              sgnPinDeallocX A.repAlloc ckCap ckPtr) ∗
              A.pool lim (M.stepEvents evs st) _ ∗
              (stackAt fsp extHookStack ∗
                (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                  memRegion (fsp - 16432#64) 48 ∗ Frame)))
            (by dsimp only [ssSender1HeadersAt]; sep_ac_rfl) ?_
          refine SepWP.weaken_pre (weaken_pool_to_freePool_2nd hevs) ?_
          refine align_pre_st (by sep_ac_rfl) ?_
          wp_done
        · conv => arg 4; rw [expose_pin_ne (pin := ⟨sg.srk.cap, sg.srk.ptr⟩) hcap]
          dsimp only [ssSender1HeadersAt]
          simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
          refine SepWP.pure_elim fun hcap_lt => ?_
          have hlayout := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
          apply sepWP_seq_lscl hcl (mid := lsρ lsRustDeallocSym)
          wp_steps_sync_pool (lsρ lsRustDeallocSym)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
          have hcall := lscall_of_withLsCl hdealloc hcl_c
          have hlive : A.repAlloc.live = A.live := rfl
          rw [hlive]
          have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
          wp_call hcall (sg.srk.ptr, sg.srk.cap.toNat, 1, M.stepEvents evs st)
          refine SepWP.align_pre_gen
            (P' := (ssSender1HeadersAt ss sg ckCap ckPtr ∗
              vecPinDeallocX A.repAlloc ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
              sgnPinDeallocX A.repAlloc ckCap ckPtr) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents sg.srk.cap.toNat 1) (M.stepEvents evs st)) _ ∗
              (stackAt fsp extHookStack ∗
                (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                  memRegion (fsp - 16432#64) 48 ∗ Frame)))
            (by dsimp only [ssSender1HeadersAt]; rw [hsp]; sep_ac_rfl) ?_
          refine SepWP.weaken_pre (weaken_dealloc_to_freePool_2nd hevs) ?_
          refine align_pre_st (by sep_ac_rfl) ?_
          wp_done
      · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
        refine seq_clean_lscl_mk_st hcl1 (mid := (blkPl_6).base + 124#64)
          (P_mid := fun sm =>
            (ssSender1HeadersAt ss sg ckCap ckPtr ∗ sgnPinDeallocX A.repAlloc ckCap ckPtr) ∗
            freePool A lim st sm ∗ stackAt fsp extHookStack ∗
            (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
              memRegion (fsp - 16432#64) 48 ∗ Frame))
          (Q := ssPresQ s0 fsp ss) ?_ ?_
        · refine sepWP_elim_freePool fun evs hevs => ?_
          by_cases hcap : (sg.priv.cap == 0#64) = true
          · conv => arg 4; rw [expose_pin_zero (pin := ⟨sg.priv.cap, sg.priv.ptr⟩) hcap]
            dsimp only [ssSender1HeadersAt]
            wp_steps_sync_pool ((blkPl_6).base + 124#64)
            refine SepWP.align_pre_gen
              (P' := (ssSender1HeadersAt ss sg ckCap ckPtr ∗ sgnPinDeallocX A.repAlloc ckCap ckPtr) ∗
                A.pool lim (M.stepEvents evs st) _ ∗
                (stackAt fsp extHookStack ∗
                  (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                    memRegion (fsp - 16432#64) 48 ∗ Frame)))
              (by dsimp only [ssSender1HeadersAt]; sep_ac_rfl) ?_
            refine SepWP.weaken_pre (weaken_pool_to_freePool_2nd hevs) ?_
            refine align_pre_st (by sep_ac_rfl) ?_
            wp_done
          · conv => arg 4; rw [expose_pin_ne (pin := ⟨sg.priv.cap, sg.priv.ptr⟩) hcap]
            dsimp only [ssSender1HeadersAt]
            simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
            refine SepWP.pure_elim fun hcap_lt => ?_
            have hlayout := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
            apply sepWP_seq_lscl hcl1 (mid := lsρ lsRustDeallocSym)
            wp_steps_sync_pool (lsρ lsRustDeallocSym)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
            have hcall := lscall_of_withLsCl hdealloc hcl_c
            have hlive : A.repAlloc.live = A.live := rfl
            rw [hlive]
            have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
            wp_call hcall (sg.priv.ptr, sg.priv.cap.toNat, 1, M.stepEvents evs st)
            refine SepWP.align_pre_gen
              (P' := (ssSender1HeadersAt ss sg ckCap ckPtr ∗ sgnPinDeallocX A.repAlloc ckCap ckPtr) ∗
                A.pool lim (M.stepEvents (rustDeallocEvents sg.priv.cap.toNat 1) (M.stepEvents evs st)) _ ∗
                (stackAt fsp extHookStack ∗
                  (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                    memRegion (fsp - 16432#64) 48 ∗ Frame)))
              (by dsimp only [ssSender1HeadersAt]; rw [hsp_1]; sep_ac_rfl) ?_
            refine SepWP.weaken_pre (weaken_dealloc_to_freePool_2nd hevs) ?_
            refine align_pre_st (by sep_ac_rfl) ?_
            wp_done
        · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
          refine seq_clean_lscl_mk_st hcl2 (mid := (blkPl_6).base + 148#64)
            (P_mid := fun sm =>
              vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
              freePool A lim st sm ∗ stackAt fsp dropVecMessageKeyStackX ∗
              ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
            (Q := ssPresQ s0 fsp ss) ?_ ?_
          · have hstep3 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 148#64) s2
                ((ssSender1HeadersAt ss sg ckCap ckPtr ∗ sgnPinDeallocX A.repAlloc ckCap ckPtr) ∗
                  freePool A lim st s2 ∗ stackAt fsp extHookStack ∗
                  (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                    memRegion (fsp - 16432#64) 48 ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ ssSender1HeadersAt ss sg ckCap ckPtr ∗
                    freePool A lim st sm ∗ stackAt fsp extHookStack ∗
                    (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                      memRegion (fsp - 16432#64) 48 ∗ Frame)) ∧
                  Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
              refine sepWP_elim_freePool fun evs hevs => ?_
              by_cases hcap : ckCap.slt 1#64 = true
              · conv => arg 4; rw [expose_sgn_zero hcap]
                dsimp only [ssSender1HeadersAt]
                wp_steps_sync_pool ((blkPl_6).base + 148#64)
                refine SepWP.align_pre_gen
                  (P' := ssSender1HeadersAt ss sg ckCap ckPtr ∗
                    A.pool lim (M.stepEvents evs st) _ ∗
                    (stackAt fsp extHookStack ∗
                      (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                        memRegion (fsp - 16432#64) 48 ∗ Frame)))
                  (by dsimp only [ssSender1HeadersAt]; sep_ac_rfl) ?_
                refine SepWP.weaken_pre (weaken_pool_to_freePool_2nd hevs) ?_
                refine align_pre_st (by sep_ac_rfl) ?_
                wp_done
              · conv => arg 4; rw [expose_sgn_ne hcap]
                dsimp only [ssSender1HeadersAt]
                simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
                refine SepWP.pure_elim fun hcap_lt => ?_
                have hlayout := rustLayoutOk_u8_of_not_slt1 hcap hcap_lt
                apply sepWP_seq_lscl hcl2 (mid := lsρ lsRustDeallocSym)
                wp_steps_sync_pool (lsρ lsRustDeallocSym)
                apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
                have hcall := lscall_of_withLsCl hdealloc hcl_c
                have hlive : A.repAlloc.live = A.live := rfl
                rw [hlive]
                have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
                wp_call hcall (ckPtr, ckCap.toNat, 1, M.stepEvents evs st)
                refine SepWP.align_pre_gen
                  (P' := ssSender1HeadersAt ss sg ckCap ckPtr ∗
                    A.pool lim (M.stepEvents (rustDeallocEvents ckCap.toNat 1) (M.stepEvents evs st)) _ ∗
                    (stackAt fsp extHookStack ∗
                      (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                        memRegion (fsp - 16432#64) 48 ∗ Frame)))
                  (by dsimp only [ssSender1HeadersAt]; rw [hsp_2]; sep_ac_rfl) ?_
                refine SepWP.weaken_pre (weaken_dealloc_to_freePool_2nd hevs) ?_
                refine align_pre_st (by sep_ac_rfl) ?_
                wp_done
            refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
            refine Entails.trans (sepConj_mono_left (ssSender1HeadersAt_entails_memRegions_x ss sg ckCap ckPtr)) ?_
            rw [stackAt_dropVecMessageKeyX_split_alloc fsp]; exact Entails.of_eq (by sep_ac_rfl)
          · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
            have hstep4 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 156#64) s3
                (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                  freePool A lim st s3 ∗ stackAt fsp dropVecMessageKeyStackX ∗
                  ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ (memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗
                    freePool A lim st sm ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
                  Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
              refine sepWP_elim_freePool fun evs hevs => ?_
              apply sepWP_seq_lscl hcl3 (mid := lsmpl.base 3)
              wp_steps_sync_pool (lsmpl.base 3)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              intro hcl_mk
              have hdrop_mk0 := lscall_of_withLsCl hdrop_mk hcl_mk
              have hstk_eq : dropVecMessageKeyStackX =
                  CryptoVerification.LibsignalTripleRatchet.Getters.dropVecMessageKeyStackX := rfl
              rw [hstk_eq]
              wp_call hdrop_mk0 (⟨ss + 192#64, sg.mkCap, sg.mkPtr, []⟩, M.stepEvents evs st)
              refine SepWP.align_pre_gen
                (P' := (memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗
                  A.pool lim (M.stepEvents _ (M.stepEvents evs st)) _ ∗
                  (stackAt fsp dropVecMessageKeyStackX ∗ Frame))
                (by rw [hsp_3, ← hstk_eq]; sep_ac_rfl) ?_
              refine SepWP.weaken_pre (weaken_sub_to_freePool_2nd hevs (by assumption)) ?_
              refine align_pre_st (by sep_ac_rfl) ?_
              wp_done
            refine SepWP.mono hstep4 (fun sm Pm _ _ h => ?_)
            rw [← stackAt_dropVecMessageKeyX_split_alloc fsp]
            exact ⟨Entails.trans h.1 (sepConj_mono_left (ssSender1_memRegions_entails_104_x ss)), h.2⟩

private theorem drop_ss_local1_placed_tail3_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (st : M.σ) :
    ∀ (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (blkPl_6).base + 164#64 →
      s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved32Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP ((blkPC_6).rebase (blkPl_6).base H)
        ((blkPl_6).base + 232#64)
        s
        ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
          sgnPinDeallocX A.repAlloc pCap pPtr ∗
          sgnPinDeallocX A.repAlloc kCap kPtr ∗
          vecPinDeallocX A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
          freePool A lim st s ∗ stackAt fsp extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗ memRegion (ss + 96#64) 24) ∗
            freePool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  intro pCap pPtr kCap kPtr G s Frame hpc hrun hcl hpres hx19
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine seq_clean_lscl_mk_st hcl (mid := (blkPl_6).base + 188#64)
    (P_mid := fun sm =>
      (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
        sgnPinDeallocX A.repAlloc kCap kPtr ∗
        vecPinDeallocX A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
      freePool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame)
    (Q := ssPresQ s0 fsp ss) ?_ ?_
  · refine sepWP_elim_freePool fun evs hevs => ?_
    by_cases hcap : pCap.slt 1#64 = true
    · conv => arg 4; rw [expose_sgn_zero (cap := pCap) (ptr := pPtr) hcap]
      dsimp only [ssTail3HeadersAt]
      wp_steps_sync_pool ((blkPl_6).base + 188#64)
      refine SepWP.align_pre_gen
        (P' := (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
          sgnPinDeallocX A.repAlloc kCap kPtr ∗
          vecPinDeallocX A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
          A.pool lim (M.stepEvents evs st) _ ∗ (stackAt fsp extHookStack ∗ Frame))
        (by dsimp only [ssTail3HeadersAt]; sep_ac_rfl) ?_
      refine SepWP.weaken_pre (weaken_pool_to_freePool_2nd hevs) ?_
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · conv => arg 4; rw [expose_sgn_ne (cap := pCap) (ptr := pPtr) hcap]
      dsimp only [ssTail3HeadersAt]
      simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hlayout := rustLayoutOk_u8_of_not_slt1 hcap hcap_lt
      apply sepWP_seq_lscl hcl (mid := lsρ lsRustDeallocSym)
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
      have hcall := lscall_of_withLsCl hdealloc hcl_c
      have hlive : A.repAlloc.live = A.live := rfl
      rw [hlive]
      have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      wp_call hcall (pPtr, pCap.toNat, 1, M.stepEvents evs st)
      refine SepWP.align_pre_gen
        (P' := (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
          sgnPinDeallocX A.repAlloc kCap kPtr ∗
          vecPinDeallocX A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents pCap.toNat 1) (M.stepEvents evs st)) _ ∗
          (stackAt fsp extHookStack ∗ Frame))
        (by dsimp only [ssTail3HeadersAt]; rw [hsp]; sep_ac_rfl) ?_
      refine SepWP.weaken_pre (weaken_dealloc_to_freePool_2nd hevs) ?_
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean_lscl_mk_st hcl1 (mid := (blkPl_6).base + 212#64)
      (P_mid := fun sm =>
        (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
          vecPinDeallocX A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
        freePool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame)
      (Q := ssPresQ s0 fsp ss) ?_ ?_
    · refine sepWP_elim_freePool fun evs hevs => ?_
      by_cases hcap : kCap.slt 1#64 = true
      · conv => arg 4; rw [expose_sgn_zero (cap := kCap) (ptr := kPtr) hcap]
        dsimp only [ssTail3HeadersAt]
        wp_steps_sync_pool ((blkPl_6).base + 212#64)
        refine SepWP.align_pre_gen
          (P' := (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
            vecPinDeallocX A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
            A.pool lim (M.stepEvents evs st) _ ∗ (stackAt fsp extHookStack ∗ Frame))
          (by dsimp only [ssTail3HeadersAt]; sep_ac_rfl) ?_
        refine SepWP.weaken_pre (weaken_pool_to_freePool_2nd hevs) ?_
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · conv => arg 4; rw [expose_sgn_ne (cap := kCap) (ptr := kPtr) hcap]
        dsimp only [ssTail3HeadersAt]
        simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
        refine SepWP.pure_elim fun hcap_lt => ?_
        have hlayout := rustLayoutOk_u8_of_not_slt1 hcap hcap_lt
        apply sepWP_seq_lscl hcl1 (mid := lsρ lsRustDeallocSym)
        wp_steps_sync_pool (lsρ lsRustDeallocSym)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
        have hcall := lscall_of_withLsCl hdealloc hcl_c
        have hlive : A.repAlloc.live = A.live := rfl
        rw [hlive]
        have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
        wp_call hcall (kPtr, kCap.toNat, 1, M.stepEvents evs st)
        refine SepWP.align_pre_gen
          (P' := (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
            vecPinDeallocX A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
            A.pool lim (M.stepEvents (rustDeallocEvents kCap.toNat 1) (M.stepEvents evs st)) _ ∗
            (stackAt fsp extHookStack ∗ Frame))
          (by dsimp only [ssTail3HeadersAt]; rw [hsp_1]; sep_ac_rfl) ?_
        refine SepWP.weaken_pre (weaken_dealloc_to_freePool_2nd hevs) ?_
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 232#64) s2
          ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
            vecPinDeallocX A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
            freePool A lim st s2 ∗ stackAt fsp extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
              freePool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
        refine sepWP_elim_freePool fun evs hevs => ?_
        by_cases hcap : (G.alice.cap == 0#64) = true
        · conv => arg 4; rw [expose_pin_zero (pin := ⟨G.alice.cap, G.alice.ptr⟩) hcap]
          dsimp only [ssTail3HeadersAt]
          wp_steps_sync_pool ((blkPl_6).base + 232#64)
          refine SepWP.align_pre_gen
            (P' := ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
              A.pool lim (M.stepEvents evs st) _ ∗ (stackAt fsp extHookStack ∗ Frame))
            (by dsimp only [ssTail3HeadersAt]; sep_ac_rfl) ?_
          refine SepWP.weaken_pre (weaken_pool_to_freePool_2nd hevs) ?_
          refine align_pre_st (by sep_ac_rfl) ?_
          wp_done
        · conv => arg 4; rw [expose_pin_ne (pin := ⟨G.alice.cap, G.alice.ptr⟩) hcap]
          dsimp only [ssTail3HeadersAt]
          simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
          refine SepWP.pure_elim fun hcap_lt => ?_
          have hlayout := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
          apply sepWP_seq_lscl hcl2 (mid := lsρ lsRustDeallocSym)
          wp_steps_sync_pool (lsρ lsRustDeallocSym)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
          have hcall := lscall_of_withLsCl hdealloc hcl_c
          have hlive : A.repAlloc.live = A.live := rfl
          rw [hlive]
          have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
          wp_call hcall (G.alice.ptr, G.alice.cap.toNat, 1, M.stepEvents evs st)
          refine SepWP.align_pre_gen
            (P' := ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
              A.pool lim (M.stepEvents (rustDeallocEvents G.alice.cap.toNat 1) (M.stepEvents evs st)) _ ∗
              (stackAt fsp extHookStack ∗ Frame))
            (by dsimp only [ssTail3HeadersAt]; rw [hsp_2]; sep_ac_rfl) ?_
          refine SepWP.weaken_pre (weaken_dealloc_to_freePool_2nd hevs) ?_
          refine align_pre_st (by sep_ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1
          (sepConj_mono_left (ssTail3HeadersAt_entails_memRegions_x ss pCap pPtr kCap kPtr G)), h.2⟩)

/-! ## Block `6` entry verification -/

/-- Relocatable `core::ptr::drop_glue::<SessionStructure> [local#1]` (Block `6`) satisfies
`withLsCodeLoaded lsmpl (dropSessionStructureLocal1SpecX M A lim)` from `hdealloc`, `hdrop_mk`,
and `hdrop_vc`. -/
theorem drop_session_structure_local1_placed_ok_of_callees [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)))
    (hdrop_mk : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (lsmpl.base 3)
      (withLsCl lsmpl (dropVecMessageKeySpecX M A lim)))
    (hdrop_vc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (lsmpl.base 2)
      (withLsCl lsmpl (dropVecChainSpecX M A lim))) :
    DropSessionStructureLocal1PlacedOkX M A lim H := by
  unfold DropSessionStructureLocal1PlacedOkX withLsCodeLoaded dropSessionStructureLocal1SpecX
  wp_init xst s0
  obtain ⟨⟨ss, G, sessSt⟩, st⟩ := xst
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst ss
  have hfirst3 := drop_ss_local1_placed_first3_ext hdealloc
  have hsender := drop_ss_local1_placed_sender_ext hdealloc hdrop_mk
  have htail3 := drop_ss_local1_placed_tail3_ext hdealloc
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_ss_local1_split_x s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i v0 v1 v2 v3
  refine SepWP.weaken_pre
    (sepConj_mono_left
      (sessionStateAt_entails_dealloc_x A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G sessSt)) ?_
  wp_pull_exists
  rename_i pCap pPtr kCap kPtr
  refine seq_clean_lscl_mk_st hcl0 (mid := (blkPl_6).base + 12#64)
    (P_mid := fun sm =>
      (ssFirst3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDeallocX A.repAlloc ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDeallocX A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDeallocX A.repAlloc G.root) ∗
      freePool A lim st sm ∗ stackAt (s0.sp - 32#64) extHookStack ∗
      (optSenderChainAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender sessSt.senderChain ∗
        vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64)
          G.chainsCap G.chainsPtr (G.chains.zip sessSt.receiverChains) ∗
        ssTail3Dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
        ssPqPart A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G.pq ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 16512#64) 96 ∗
        ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3))
    (Q := fun sm =>
      Saved32Preserved s0 sm (s0.sp - 32#64) ∧
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · rw [stackAt_dropVecChainX_split_alloc (s0.sp - 32#64)]
    have hsp_sub : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
    rw [hsp_sub]
    wp_steps_sync_pool ((blkPl_6).base + 12#64)
    refine SepWP.align_pre_gen
      (P' := (ssFirst3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDeallocX A.repAlloc ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDeallocX A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDeallocX A.repAlloc G.root) ∗
        A.pool lim st _ ∗
        (stackAt (s0.sp - 32#64) extHookStack ∗
          (optSenderChainAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender sessSt.senderChain ∗
            vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64)
              G.chainsCap G.chainsPtr (G.chains.zip sessSt.receiverChains) ∗
            ssTail3Dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
            ssPqPart A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G.pq ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
            memRegion (s0.sp - 16512#64) 96 ∗
            ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3)))
      (by
        dsimp only [ssFirst3HeadersAt, ssTail3HeadersAt, ssTail3Dealloc, ssPqPart, ssSavedFrame,
          Reg.x19, Reg.lr, Reg.fp]
        sep_ac_rfl) ?_
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (freePool_intro A lim st _))) ?_
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨hpres1, hx0_1⟩
    refine seq_clean_lscl_mk_st hcl1 (mid := (blkPl_6).base + 76#64)
      (P_mid := fun sm =>
        optSenderChainAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender sessSt.senderChain ∗
        freePool A lim st sm ∗ stackAt (s0.sp - 32#64) dropVecMessageKeyStackX ∗
        (vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64)
          G.chainsCap G.chainsPtr (G.chains.zip sessSt.receiverChains) ∗
        ssTail3Dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
        ssPqPart A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G.pq ∗
        ssFirst3Mem (s0.readReg64 (Reg.gpr 0#5)) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 16512#64) 48 ∗
        ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3))
      (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
      ?_ ?_
    · refine SepWP.mono
        (hfirst3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align st G s1 _
          hpc1 hrun1 hcl1 hpres1 hx0_1) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      rw [stackAt_dropVecMessageKeyX_split_alloc (s0.sp - 32#64)]
      have hsp_sub1 : (s0.sp - 32#64) - 16432#64 = s0.sp - 16464#64 := by bv_omega
      rw [hsp_sub1,
          ProofLib.memRegion_split' (b := s0.sp - 16512#64) (n := 48) (k := 48)
            (b' := s0.sp - 16464#64) rfl (by bv_omega) (by decide)]
      dsimp only [ssFirst3Mem]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s2 hpc2 hrun2 hcl2 ⟨hpres2, hx19_2⟩
      refine seq_clean_lscl_mk_st hcl2 (mid := (blkPl_6).base + 156#64)
        (P_mid := fun sm =>
          vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64)
            G.chainsCap G.chainsPtr (G.chains.zip sessSt.receiverChains) ∗
          freePool A lim st sm ∗ stackAt (s0.sp - 32#64) dropVecChainStackX ∗
          (ssTail3Dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          ssPqPart A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G.pq ∗
          ssFirst3Mem (s0.readReg64 (Reg.gpr 0#5)) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
          ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3))
        (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
        ?_ ?_
      · refine SepWP.mono
          (hsender s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align st
            G.sender sessSt.senderChain s2 _ hpc2 hrun2 hcl2 hpres2 hx19_2) ?_
        intro sm Pm _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        rw [stackAt_dropVecChainX_split_mk (s0.sp - 32#64)]
        have hsp_sub2 : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
        rw [hsp_sub2]
        exact Entails.of_eq (by sep_ac_rfl)
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_clean_lscl_mk_st hcl3 (mid := (blkPl_6).base + 164#64)
          (P_mid := fun sm =>
            ssTail3Dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
            freePool A lim st sm ∗ stackAt (s0.sp - 32#64) extHookStack ∗
            (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDeallocX A.repAlloc G.pq) ∗
            ssFirst3Mem (s0.readReg64 (Reg.gpr 0#5)) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
            memRegion (s0.sp - 16512#64) 96 ∗
            ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3)
          (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
          ?_ ?_
        · have hs3_align : (s3.sp &&& 15#64 == 0#64) = true := by
            rw [hsp_3]; exact hfsp_align
          refine sepWP_elim_freePool fun evs hevs => ?_
          apply sepWP_seq_lscl hcl3 (mid := lsmpl.base 2)
          wp_steps_sync_pool (lsmpl.base 2)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro hcl_vc
          have hdrop_vc_w : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (lsmpl.base 2)
              (withLsCl lsmpl (dropVecChainSpecX M A lim)) := hdrop_vc
          have hdrop_vc0 := lscall_of_withLsCl hdrop_vc_w hcl_vc
          have hstk_vc : dropVecChainStackX =
              CryptoVerification.LibsignalTripleRatchet.Getters.dropVecChainStackX := rfl
          rw [hstk_vc]
          wp_call hdrop_vc0 (⟨s0.readReg64 (Reg.gpr 0#5) + 72#64, G.chainsCap, G.chainsPtr,
            G.chains.zip sessSt.receiverChains⟩, M.stepEvents evs st)
          have hsp_sub3 : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
          refine SepWP.align_pre_gen
            (P' := ssTail3Dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
              A.pool lim (M.stepEvents _ (M.stepEvents evs st)) _ ∗
              (stackAt (s0.sp - 32#64) extHookStack ∗
                (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
                  ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDeallocX A.repAlloc G.pq) ∗
                ssFirst3Mem (s0.readReg64 (Reg.gpr 0#5)) ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
                memRegion (s0.sp - 16512#64) 96 ∗
                ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3))
            (by
              rw [hsp_3, ← hstk_vc, stackAt_dropVecChainX_split_alloc (s0.sp - 32#64), hsp_sub3]
              dsimp only [ssTail3HeadersAt, ssTail3Dealloc, ssPqPart, ssFirst3Mem, ssSavedFrame]
              sep_ac_rfl) ?_
          refine SepWP.weaken_pre (weaken_sub_to_freePool_2nd hevs (by assumption)) ?_
          refine align_pre_st (by sep_ac_rfl) ?_
          wp_done
        · intro s4 hpc4 hrun4 hcl4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          refine seq_clean_lscl_mk_st hcl4 (mid := (blkPl_6).base + 232#64)
            (P_mid := fun sm =>
              (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
                ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDeallocX A.repAlloc G.pq) ∗
              freePool A lim st sm ∗
              (ss9MemRegions (s0.readReg64 (Reg.gpr 0#5)) ∗
                stackAt (s0.sp - 32#64) dropVecChainStackX ∗
                ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3))
            (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
            ?_ ?_
          · refine SepWP.mono
              (htail3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align st
                pCap pPtr kCap kPtr G s4 _ hpc4 hrun4 hcl4
                ⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
                hx19_4) ?_
            intro sm Pm _ _ h
            refine ⟨Entails.trans h.1 ?_, h.2⟩
            rw [stackAt_dropVecChainX_split_alloc (s0.sp - 32#64)]
            have hsp_sub4 : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
            rw [hsp_sub4]
            dsimp only [ss9MemRegions, ssFirst3Mem]
            exact Entails.of_eq (by sep_ac_rfl)
          · intro s5 hpc5 hrun5 hcl5 ⟨⟨hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
            refine sepWP_elim_freePool fun evs hevs => ?_
            by_cases hcap : (G.pq.cap == 0#64) = true
            · conv => arg 4; rw [expose_pin_zero (pin := G.pq) hcap]
              dsimp only [ssSavedFrame]
              wp_steps_sync_pool (s0.readReg64 .lr)
              refine SepWP.align_pre_gen
                (P' := (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
                  ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ emp) ∗
                  A.pool lim (M.stepEvents evs st) _ ∗
                  (ss9MemRegions (s0.readReg64 (Reg.gpr 0#5)) ∗
                    stackAt (s0.sp - 32#64) dropVecChainStackX ∗
                    (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3))))
                (by sep_ac_rfl) ?_
              refine SepWP.weaken_pre
                (ss_epilogue_cap0_weaken hevs (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr
                  s0.sp _ _ _ _ _) ?_
              dsimp only [freePool]
              wp_done
            · conv => arg 4; rw [expose_pin_ne (pin := G.pq) hcap]
              dsimp only [ssSavedFrame]
              simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
              refine SepWP.pure_elim fun hcap_lt => ?_
              have hlayout := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
              apply sepWP_seq_lscl hcl5 (mid := lsρ lsRustDeallocSym)
              wp_steps_sync_pool (lsρ lsRustDeallocSym)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              intro hcl_tail
              have hdealloc_w : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (lsρ lsRustDeallocSym)
                  (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)) := hdealloc
              have hdealloc0 := lscall_of_withLsCl hdealloc_w hcl_tail
              have hlive : A.repAlloc.live = A.live := rfl
              rw [hlive]
              refine SepWP.align_pre_gen
                (P' := ((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
                  ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗
                  (A.live G.pq.ptr G.pq.cap.toNat 1 ∗ memRegion G.pq.ptr G.pq.cap.toNat) ∗
                  ss9MemRegions (s0.readReg64 (Reg.gpr 0#5)) ∗
                  A.pool lim (M.stepEvents evs st) _ ∗
                  stackAt (s0.sp - 32#64) dropVecChainStackX ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3))
                (by sep_ac_rfl) ?_
              refine SepWP.weaken_pre
                (tail_dealloc_ss_local1_pre_weaken_ext (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr
                  (A.live G.pq.ptr G.pq.cap.toNat 1 ∗ memRegion G.pq.ptr G.pq.cap.toNat)
                  (ss9MemRegions (s0.readReg64 (Reg.gpr 0#5))) _ s0.sp _ _ _ _) ?_
              have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
              wp_call hdealloc0 (G.pq.ptr, G.pq.cap.toNat, 1, M.stepEvents evs st)
              refine SepWP.align_pre_gen
                (P' := (memRegion (s0.readReg64 (Reg.gpr 0#5) + 120#64) 24 ∗
                  ss9MemRegions (s0.readReg64 (Reg.gpr 0#5))) ∗
                  A.pool lim (M.stepEvents (rustDeallocEvents G.pq.cap.toNat 1) (M.stepEvents evs st)) _ ∗
                  (memRegion (s0.sp - 16512#64) 128 ∗ stackAt s0.sp extHookStack))
                (by
                  have hsp_ret : (s0.sp - 32#64) + 32#64 = s0.sp := by bv_omega
                  try rw [hsp_ret]
                  sep_ac_rfl) ?_
              refine SepWP.weaken_pre
                (ss_epilogue_dealloc_post_weaken hevs (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap.toNat
                  s0.sp _) ?_
              dsimp only [freePool]
              wp_done

/-- Relocatable `core::ptr::drop_glue::<SessionStructure> [local#1]` (Block `6`) satisfies
`withLsCodeLoaded lsmpl (dropSessionStructureLocal1SpecX M A lim)` under
`AllocContractsPlaced M A lim H`. -/
theorem drop_session_structure_local1_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H) :
    DropSessionStructureLocal1PlacedOkX M A lim H :=
  drop_session_structure_local1_placed_ok_of_callees
    (hA.dealloc (callerProg := (blkPC_6).rebase (blkPl_6).base H))
    (drop_vec_message_key_placed_ok_cl (callerProg := (blkPC_6).rebase (blkPl_6).base H) hA)
    (drop_vec_chain_placed_ok_cl (callerProg := (blkPC_6).rebase (blkPl_6).base H) hA)

theorem drop_session_structure_local1_placed_ok_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 6)
      (withLsCl lsmpl (dropSessionStructureLocal1SpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (drop_session_structure_local1_placed_ok_ext hA)

theorem drop_session_structure_local1_placed_ok_of_serContracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    DropSessionStructureLocal1PlacedOkX M A lim H :=
  drop_session_structure_local1_placed_ok_ext hC.alloc

theorem drop_session_structure_local1_placed_ok_of_stage2 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : Stage2ContractsPlaced A lim H) :
    DropSessionStructureLocal1PlacedOkX M A lim H :=
  drop_session_structure_local1_placed_ok_of_serContracts
    (serContractsXPlaced_of_stage2ContractsPlaced hC)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1ExtBudget
