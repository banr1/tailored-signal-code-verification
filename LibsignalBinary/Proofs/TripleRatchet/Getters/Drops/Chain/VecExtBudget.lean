/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExt
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.ExtBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable Contract for `drop_glue<Vec<Chain>>`

Proves the `RustCliAllocBudget`-threaded `[LibsignalPlacement]` contract `dropVecChainSpec`
for `core::ptr::drop_glue::<alloc::vec::Vec<...::Chain>>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExtBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ReceiverChain)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement lsmpl lsρ
  withLsCodeLoaded sepWP_seq_lscl
  subroutine_ok_withLsCodeLoaded_of_plain ls_subroutine_ok_of_block
)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecAt)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt messageKeyAt)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  blkPC_2 blkPl_2 blkPC_3 blkPl_3
  dropVecChainStack dropVecMessageKeyStack
  lsRustDeallocSym ls_hook_ok_rustDealloc
)
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts (
  Saved48Preserved stackAt_dropVecChain_split
  vecPinDealloc ckDealloc chainOuterHeadersAt
  chainOuterHeadersAt_entails_memRegions chain_memRegions_entails_104
  chainAt_entails_dealloc vecAt_expose_loop post_loop_weaken
  header24_weaken cells6_sub48_entails
  cap0_weaken_48_vecChain vecChain_tail_dealloc_post
  ofNat_succ_eq_add_one ofNat_beq_zero_false ofNat_add_one_beq_one_false
  tail_len_mul_lt cons_len_mul add_104_add_48
  sep_pull_body sep_push_body sep_rejoin_loop
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs PoolPreserved
  RustCliAllocBudget VmPreserved rustDeallocEvents rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropVecChainSpec dropVecMessageKeySpec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.ExtBudget (
  drop_vec_message_key_placed_ok
)

attribute [local irreducible] Program.fetch Program.externAt?

private def freeOnlyPool {M : AllocCostModel} (A : RustCliAllocBudget M)
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

private theorem freeOnlyPool_append {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs₁ evs₂ : List AllocEvent}
    (h1 : FreeOnlyEvs evs₁) (h2 : FreeOnlyEvs evs₂) {s sm : State}
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]) :
    A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s ⊢
      freeOnlyPool A lim st sm := by
  rw [← A.pool_of_vmPreserved hvm, ← M.stepEvents_append evs₁ evs₂ st]
  exact Entails.sepExists_right (evs₁ ++ evs₂)
    (Entails.pure_right (FreeOnlyEvs.append h1 h2) (Entails.refl _))

private theorem freeOnlyPool_dealloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    (sz al : Nat) {s sm : State}
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]) :
    A.pool lim (M.stepEvents (rustDeallocEvents sz al) (M.stepEvents evs st)) s ⊢
      freeOnlyPool A lim st sm :=
  freeOnlyPool_append A lim st hevs (FreeOnlyEvs.singleton al sz) hvm

private theorem SepWP.seq_state {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 (fun sm _Pm hpcm hrunm ⟨hent, hq⟩ =>
    SepWP.weaken_pre hent (h2 sm hpcm hrunm hq))

private theorem seq_state_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
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

private theorem SepWP.unpack_freeOnlyPool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {target : BitVec 64} {s : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = freeOnlyPool A lim st s ∗ Frame := by sep_focus)
    (hk : ∀ evs : List AllocEvent, FreeOnlyEvs evs →
      SepWP prog target s (A.pool lim (M.stepEvents evs st) s ∗ Frame) post) :
    SepWP prog target s P post := by
  rw [hf]; unfold freeOnlyPool
  wp_pull_exists
  rename_i evs
  exact SepWP.pure_elim (hk evs)

private theorem SepWP.fold_keep {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim (M.stepEvents evs st) s ∗ Frame := by sep_focus)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (freeOnlyPool A lim st sm ∗ Frame) post) :
    SepWP prog target sm P post :=
  SepWP.focus_weaken (freeOnlyPool_keep A lim st hevs hvm) hf hk

private theorem SepWP.fold_append {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {evs₁ evs₂ : List AllocEvent} (h1 : FreeOnlyEvs evs₁)
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s ∗ Frame := by sep_focus)
    (h2 : FreeOnlyEvs evs₂ := by assumption)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (freeOnlyPool A lim st sm ∗ Frame) post) :
    SepWP prog target sm P post :=
  SepWP.focus_weaken (freeOnlyPool_append A lim st h1 h2 hvm) hf hk

private theorem SepWP.fold_dealloc {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {evs : List AllocEvent} (hevs : FreeOnlyEvs evs) (sz al : Nat)
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim (M.stepEvents (rustDeallocEvents sz al) (M.stepEvents evs st)) s ∗ Frame := by sep_focus)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (freeOnlyPool A lim st sm ∗ Frame) post) :
    SepWP prog target sm P post :=
  SepWP.focus_weaken (freeOnlyPool_dealloc A lim st hevs sz al hvm) hf hk

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

private theorem SepWP.mono_ac {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {post post' : State → SepProp → Prop}
    (h1 : SepWP prog target s P' post)
    (h2 : ∀ sf Pf, sf.pc = target → sf.status = .Running → post sf Pf → post' sf Pf)
    (heq : P = P') :
    SepWP prog target s P post' :=
  SepWP.weaken_pre (Entails.of_eq heq) (SepWP.mono h1 h2)

private theorem stackAt_dropVecMessageKey_split_bottom (fsp : BitVec 64) :
    stackAt fsp dropVecMessageKeyStack =
      memRegion (fsp - 4144#64) 48 ∗ stackAt fsp allocHookStack := by
  rw [← stackAt_split_bottom fsp allocHookStack 48 (by decide)]
  rfl

private theorem tail_stack_96_from_bottom (sp : BitVec 64) :
    memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack =
      stackAt (sp - 48#64) dropVecMessageKeyStack ∗ cells (sp - 48#64) 6 := by
  rw [← stackAt_split_bottom sp allocHookStack 96 (by decide),
      show allocHookStack + 96 = dropVecChainStack from rfl,
      ← stackAt_dropVecChain_split sp]

private theorem cells6_vecChain_entails_stack_bottom (sp : BitVec 64)
    (fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) dropVecMessageKeyStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack := by
  rw [tail_stack_96_from_bottom sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

private theorem tail_dealloc_vecChain_pre_weaken (v cap ptr : BitVec 64) (Live Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      Live ∗ Pool ∗
      stackAt (sp - 48#64) dropVecMessageKeyStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    Pool ∗ Live ∗ stackAt sp allocHookStack ∗
      (memRegion v 24 ∗ memRegion (sp - 4192#64) 96) := by
  refine Entails.trans (header24_weaken v cap ptr _) ?_
  have hstk := cells6_vecChain_entails_stack_bottom sp fp lr x22 x21 x20 x19
  have hgroup :
      (memRegion v 24 ∗ Live ∗ Pool ∗
        stackAt (sp - 48#64) dropVecMessageKeyStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      ((stackAt (sp - 48#64) dropVecMessageKeyStack ∗
          ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
          ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ∗
        (Pool ∗ Live ∗ memRegion v 24)) := by sep_ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_left hstk) ?_
  exact Entails.of_eq (by sep_ac_rfl)

private theorem drop_vec_chain_placed_body [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdrop_mk : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsmpl.base 3) (withLsCodeLoaded lsmpl (dropVecMessageKeySpec M A lim)))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (g : ChainGhost) (c : ReceiverChain)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_2).base + 56#64 →
      s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 →
      s.readReg64 .x22 = cnt →
      SepWP ((blkPC_2).rebase (blkPl_2).base H)
        ((blkPl_2).base + 44#64)
        s
        (chainAt A.repAlloc (g, c) cur ∗ freeOnlyPool A lim st s ∗
          stackAt fsp dropVecMessageKeyStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗ freeOnlyPool A lim st sm ∗
            stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧
          sm.readReg64 .x22 = cnt) := by
  simp only [rustCliDeallocBudgetSpec] at hdealloc
  simp only [withLsCodeLoaded, dropVecMessageKeySpec] at hdrop_mk
  intro cur cnt g c s Frame hpc hrun hcl hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (chainAt_entails_dealloc A.repAlloc cur g c)) ?_
  wp_pull_exists
  rename_i ckCap ckPtr
  rw [stackAt_dropVecMessageKey_split_bottom fsp]
  refine seq_state_lscl hcl (mid := (blkPl_2).base + 76#64) (P_mid := fun sm =>
    (chainOuterHeadersAt cur g ckCap ckPtr ∗
      vecPinDealloc A.repAlloc ⟨g.priv.cap, g.priv.ptr⟩ ∗
      ckDealloc A.repAlloc ckCap ckPtr) ∗
    freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗
    (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
      memRegion (fsp - 4144#64) 48 ∗ Frame))
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt)
    ?_ ?_
  · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
    dsimp only [chainOuterHeadersAt, vecPinDealloc, ckDealloc]
    by_cases hcap : (g.srk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
    · wp_steps
      refine SepWP.fold_keep hevs (hk := ?_)
      wp_done
    · wp_steps
      refine SepWP.sync_pool (hk := ?_)
      rw [← hsp]
      wp_call hdealloc (g.srk.ptr, g.srk.cap.toNat, 1, M.stepEvents evs st)
      have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace
      refine SepWP.fold_dealloc hevs g.srk.cap.toNat 1 (hk := ?_)
      refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp]; try sep_ac_rfl)) ?_
      wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
    refine seq_state_lscl hcl1 (mid := (blkPl_2).base + 96#64) (P_mid := fun sm =>
      (chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDealloc A.repAlloc ckCap ckPtr) ∗
      freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗
      (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
        memRegion (fsp - 4144#64) 48 ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt)
      ?_ ?_
    · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      dsimp only [chainOuterHeadersAt, vecPinDealloc, ckDealloc]
      by_cases hcap : (g.priv.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      · wp_steps
        refine SepWP.fold_keep hevs (hk := ?_)
        wp_done
      · wp_steps
        refine SepWP.sync_pool (hk := ?_)
        rw [← hsp_1]
        wp_call hdealloc (g.priv.ptr, g.priv.cap.toNat, 1, M.stepEvents evs st)
        have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_1
        refine SepWP.fold_dealloc hevs g.priv.cap.toNat 1 (hk := ?_)
        refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp_1]; try sep_ac_rfl)) ?_
        wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine seq_state_lscl hcl2 (mid := (blkPl_2).base + 36#64) (P_mid := fun sm =>
        vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
        freeOnlyPool A lim st sm ∗ stackAt fsp dropVecMessageKeyStack ∗
        ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt)
        ?_ ?_
      · have hstep3 : SepWP ((blkPC_2).rebase (blkPl_2).base H) ((blkPl_2).base + 36#64) s2
            ((chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDealloc A.repAlloc ckCap ckPtr) ∗
              freeOnlyPool A lim st s2 ∗ stackAt fsp allocHookStack ∗
              (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
                memRegion (fsp - 4144#64) 48 ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ chainOuterHeadersAt cur g ckCap ckPtr ∗
                freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗
                (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
                  memRegion (fsp - 4144#64) 48 ∗ Frame)) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
          dsimp only [chainOuterHeadersAt, ckDealloc]
          by_cases hcap : ckCap.slt 1#64 = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
          · wp_steps
            refine SepWP.fold_keep hevs (hk := ?_)
            wp_done
          · wp_steps
            refine SepWP.sync_pool (hk := ?_)
            rw [← hsp_2]
            wp_call hdealloc (ckPtr, ckCap.toNat, 1, M.stepEvents evs st)
            have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_2
            wp_steps
            refine SepWP.fold_dealloc hevs ckCap.toNat 1 (hk := ?_)
            refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp_2]; try sep_ac_rfl)) ?_
            wp_done
        refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
        refine Entails.trans (sepConj_mono_left (chainOuterHeadersAt_entails_memRegions cur g ckCap ckPtr)) ?_
        rw [stackAt_dropVecMessageKey_split_bottom fsp]
        exact Entails.of_eq (by sep_ac_rfl)
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        rw [← stackAt_dropVecMessageKey_split_bottom fsp]
        have hstep4 : SepWP ((blkPC_2).rebase (blkPl_2).base H) ((blkPl_2).base + 44#64) s3
            (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
              freeOnlyPool A lim st s3 ∗ stackAt fsp dropVecMessageKeyStack ∗
              ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ (memRegion (cur + 48#64) 24 ∗ memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗
                freeOnlyPool A lim st sm ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
          wp_steps
          refine SepWP.sync_pool (hk := ?_)
          rw [← hsp_3]
          wp_call hdrop_mk (⟨cur + 48#64, g.mkCap, g.mkPtr, g.keys.zip c.messageKeys⟩, M.stepEvents evs st)
          have htr_m : sf.trace = s0.trace := (by assumption : sf.trace = _).trans htrace_3
          refine SepWP.fold_append hevs (hk := ?_)
          refine SepWP.weaken_pre (Entails.of_eq (by rw [hsp_3]; try sep_ac_rfl)) ?_
          wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (chain_memRegions_entails_104 cur)), h.2⟩)

private theorem drop_vec_chain_placed_loop [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdrop_mk : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsmpl.base 3) (withLsCodeLoaded lsmpl (dropVecMessageKeySpec M A lim)))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (ChainGhost × ReceiverChain)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (blkPl_2).base + 56#64 →
      s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      SepWP ((blkPC_2).rebase (blkPl_2).base H)
        ((blkPl_2).base + 124#64)
        s
        (arrayAt (chainAt A.repAlloc) 104 cur rest ∗ freeOnlyPool A lim st s ∗
          stackAt fsp dropVecMessageKeyStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ freeOnlyPool A lim st sm ∗
            stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v) := by
  have hbody := drop_vec_chain_placed_body (st := st) hdealloc hdrop_mk s0 fsp v ptr hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨g, c⟩
    intro cur s Frame _ hlen hpc hrun hcl hpres hx19 hx20 hx21 hx22
    rw [show arrayAt (chainAt A.repAlloc) 104 cur ((g, c) :: tl) =
          chainAt A.repAlloc (g, c) cur ∗ arrayAt (chainAt A.repAlloc) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine seq_state_lscl hcl (mid := (blkPl_2).base + 44#64)
      (hbody cur (BitVec.ofNat 64 ((g, c) :: tl).length) g c s
        (arrayAt (chainAt A.repAlloc) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hcl hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 hcl4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4, hx21_4, hx22_4⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx22_4 ⊢
      refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      wp_steps
      refine SepWP.fold_keep hevs (hk := ?_)
      wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show ((g, c) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx22_4
      have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
      refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      wp_steps
      refine SepWP.fold_keep hevs (hk := ?_)
      apply SepWP.mono_ac
      · exact ih (cur + 104#64) _ (memRegion cur 104 ∗ Frame)
          htl_ne htl_len rfl (by assumption) hcl4
          ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
          hx19_4 hx20_4
          (by simp only [wp_norm, arm64_norm, add_104_add_48]) rfl
      · intro sf Pf _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        have hsplit := cons_len_mul (g, c) (hd2 :: tl2) 104
        have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
        exact Entails.refl _
      · sep_ac_rfl

theorem drop_vec_chain_placed_ok_of_dealloc_and_mk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdrop_mk_raw : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsmpl.base 3) (withLsCodeLoaded lsmpl (dropVecMessageKeySpec M A lim))) :
    subroutine_ok ((blkPC_2).rebase (blkPl_2).base H) (blkPl_2).base
      (withLsCodeLoaded lsmpl (dropVecChainSpec M A lim)) := by
  simp only [withLsCodeLoaded, dropVecChainSpec]
  have hdealloc := hdealloc_raw
  simp only [rustCliDeallocBudgetSpec] at hdealloc
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, cs⟩, st⟩
  have hloop := drop_vec_chain_placed_loop (st := st) hdealloc_raw hdrop_mk_raw
  dsimp only at *
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = v := by assumption
  subst hx0
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropVecChain_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop A.repAlloc 104 8 (chainAt A.repAlloc)
      (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine SepWP.seq_state (mid := (blkPl_2).base + 124#64)
    (P_mid := fun sm =>
      (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
      memRegion ptr (cs.length * 104) ∗
      (if cap = 0 then emp
       else A.repAlloc.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) ∗
      freeOnlyPool A lim st sm ∗
      stackAt (s0.sp - 48#64) dropVecMessageKeyStack ∗
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
      simp only [State.setMem_setMem]
      apply SepWP.fold (freeOnlyPool_intro A lim st _) (by sep_focus)
      wp_done
    | cons hd tl =>
      have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
      apply sepWP_seq_lscl hcl0 (mid := (blkPl_2).base + 56#64)
      wp_steps_sync_pool ((blkPl_2).base + 56#64)
      simp only [State.setMem_setMem]
      apply SepWP.fold (freeOnlyPool_intro A lim st _) (by sep_focus)
      apply SepWP.done
      · wp_norm_lhs
      · wp_norm_lhs
      intro hcl_loop
      apply SepWP.mono_ac
      · exact hloop s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) ptr hfsp_align
          (hd :: tl) ptr _
          ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
            (if cap = 0 then emp
             else A.repAlloc.live ptr (cap.toNat * 104) 8 ∗
               memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 104)) ((cap.toNat - (hd :: tl).length) * 104)) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
          (List.cons_ne_nil _ _) hlen_lt rfl (by assumption) hcl_loop
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          rfl rfl rfl rfl
      · intro sm Pm _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        exact Entails.of_eq (by sep_ac_rfl)
      · sep_ac_rfl
  · intro sm hpcm hrunm ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hx19, hx20⟩
    refine SepWP.weaken_pre (post_loop_weaken A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs.length hlen_le hcap_lt _) ?_
    refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      wp_steps
      refine SepWP.fold_keep hevs (hk := ?_)
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (cap0_weaken_48_vecChain (s0.readReg64 (Reg.gpr 0#5)) 0#64 ptr _ s0.sp _ _ _ _ _ _)) ?_
      unfold freeOnlyPool
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      wp_steps
      have hmul : 104#64 * cap = BitVec.ofNat 64 (cap.toNat * 104) := by bv_omega
      refine SepWP.sync_pool (hk := ?_)
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (tail_dealloc_vecChain_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) cap ptr
          (A.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104))
          (A.pool lim (M.stepEvents evs st) _) s0.sp _ _ _ _ _ _)) ?_
      wp_call hdealloc (ptr, cap.toNat * 104, 8, M.stepEvents evs st)
      have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace
      refine SepWP.fold_dealloc hevs (cap.toNat * 104) 8 (hk := ?_)
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (vecChain_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) (freeOnlyPool A lim st sf) s0.sp)) ?_
      unfold freeOnlyPool
      wp_done

theorem drop_vec_chain_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_2).rebase (blkPl_2).base H) (blkPl_2).base
      (withLsCodeLoaded lsmpl (dropVecChainSpec M A lim)) := by
  have hmk0 : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H) (lsmpl.base 3)
      (dropVecMessageKeySpec M A lim) :=
    drop_vec_message_key_placed_ok h_dealloc
  have hmk := ls_subroutine_ok_of_block (callerProg := (blkPC_2).rebase (blkPl_2).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain hmk0)
  exact drop_vec_chain_placed_ok_of_dealloc_and_mk (ls_hook_ok_rustDealloc h_dealloc) hmk

end LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExtBudget
