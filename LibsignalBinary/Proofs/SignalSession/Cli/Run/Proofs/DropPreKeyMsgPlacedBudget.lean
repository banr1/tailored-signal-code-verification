/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsgPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsgBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsg.HelpersBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs

/-!
# Budget-Threaded Relocatable Drop Glue Proof for `PreKeySignalMessage`

Proves the `RustCliAllocBudget M` contract `dropPreKeyMsgSpecPlaced` for
`core::ptr::drop_glue::<PreKeySignalMessage>` under `[LibsignalPlacement]` and transfers it to
caller blocks `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsgPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ
)
open CryptoVerification.RustHeap (LayoutOk)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApiRepr (PreKeyMsgGhost preKeyMsgAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded ls_subroutine_ok_rocl_of_block sepWP_seq_lscro
  withLsCodeRoLoaded withLsRoCl
)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.Placed (
  blkLib_555 blkPl_555 instIsLsBlockProg_555 lsProg_555
)
open CryptoVerification.SignalSession.Cli.RunProofs (DropPreKeyMsgGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.DropPreKeyMsgHelpers (
  optSliceDeallocX pkmHeadersAt pkmHeadersAt_entails_memRegion_248
  preKeyMsgAt_entails_deallocX sliceDeallocX subroutine_ok_map_frame_weaken
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk
  rustDeallocEvents
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsgBudget (dropPreKeyMsgSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsg.HelpersBudget (
  dropPreKeyMsgExactSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (dealloc_lscro_of_cli)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

/-- Budget-threaded `[LibsignalPlacement]` specification for `drop_glue::<PreKeySignalMessage>`. -/
def dropPreKeyMsgSpecPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (DropPreKeyMsgGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl { dropPreKeyMsgSpec M A lim stk with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗ preKeyMsgAt A.repAlloc x.g x.a x.m ∗
        A.pool lim st s ∗ stackAt s.sp stk }

section DropPreKeyMsgPlacedBudgetHelpers

private def freeOnlyPool {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent,
    ⌜∀ ev ∈ evs, ∃ al sz, ev = .free al sz⌝ ∗ A.pool lim (M.stepEvents evs st) s

private theorem freeOnlyPool_intro_nil {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ freeOnlyPool A lim st s := by
  unfold freeOnlyPool
  refine Entails.sepExists_right [] ?_
  rw [M.stepEvents_nil]
  exact Entails.pure_right (by intro _ h; cases h) (Entails.refl _)

private theorem freeOnlyPool_step_dealloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (evs : List AllocEvent)
    (hevs : ∀ ev ∈ evs, ∃ al sz, ev = .free al sz) (sz al : Nat) :
    A.pool lim (M.stepEvents (rustDeallocEvents sz al) (M.stepEvents evs st)) s ⊢
      freeOnlyPool A lim st s := by
  unfold freeOnlyPool
  refine Entails.sepExists_right (evs ++ rustDeallocEvents sz al) ?_
  rw [M.stepEvents_append]
  refine Entails.pure_right ?_ (Entails.refl _)
  intro ev hmem
  rcases List.mem_append.mp hmem with h1 | h2
  · exact hevs ev h1
  · simp only [rustDeallocEvents, List.mem_singleton] at h2
    exact ⟨al, sz, h2⟩

private theorem freeOnlyPool_keep {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (evs : List AllocEvent)
    (hevs : ∀ ev ∈ evs, ∃ al sz, ev = .free al sz) :
    A.pool lim (M.stepEvents evs st) s ⊢ freeOnlyPool A lim st s := by
  unfold freeOnlyPool
  exact Entails.sepExists_right evs (Entails.pure_right hevs (Entails.refl _))

private theorem stackAt_pkm_split_placed (sp : BitVec 64) :
    stackAt sp (32 + extHookStack) =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

private theorem tail_stack_32_from_bottomX_placed (sp : BitVec 64) :
    memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 := by
  rw [show (16416#64 : BitVec 64) = BitVec.ofNat 64 (extHookStack + 32) from rfl,
      ← ProofLib.stackAt_split_bottom sp extHookStack 32 (by decide),
      show extHookStack + 32 = 32 + extHookStack from rfl,
      ← stackAt_pkm_split_placed sp]

private theorem cells4_entails_stack_bottomX_placed (sp fp lr x19 c3 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ c3) ⊢
    memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack := by
  rw [tail_stack_32_from_bottomX_placed sp]
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x19 (Entails.sepExists_right c3 (Entails.refl _))))

private theorem stack_restore_32X_placed (sp fp lr x19 c3 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ c3) ⊢
    stackAt sp (32 + extHookStack) := by
  rw [stackAt_pkm_split_placed sp, ← tail_stack_32_from_bottomX_placed sp]
  exact cells4_entails_stack_bottomX_placed sp fp lr x19 c3

private theorem sliceDeallocX_eq_placed (A : CryptoVerification.RustHeap.RustAlloc)
    (ptr sz : BitVec 64) :
    sliceDeallocX A ptr sz =
      if (sz == 0#64) = true then emp
      else ⌜0 < sz.toNat ∧ sz.toNat < 2 ^ 63⌝ ∗ A.live ptr sz.toNat 1 ∗ memRegion ptr sz.toNat :=
  rfl

private theorem optSliceDeallocX_eq_placed (A : CryptoVerification.RustHeap.RustAlloc)
    (ptr sz : BitVec 64) :
    optSliceDeallocX A ptr sz =
      if (ptr == 0#64) = true then emp else sliceDeallocX A ptr sz :=
  rfl

private theorem pkm_empty_epilogue_weaken_placed
    (a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen : BitVec 64)
    (Pool : SepProp) (sp fp lr x19 c3 : BitVec 64) :
    pkmHeadersAt a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen ∗
      Pool ∗ stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ c3) ⊢
    memRegion a 248 ∗ Pool ∗ stackAt sp (32 + extHookStack) := by
  have hh := pkmHeadersAt_entails_memRegion_248
    a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen
  have hs := stack_restore_32X_placed sp fp lr x19 c3
  exact sepConj_mono hh (sepConj_mono_right hs)

private theorem pkm_tail_dealloc_pre_weaken_placed
    (a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen : BitVec 64)
    (Live Pool : SepProp) (sp fp lr x19 c3 : BitVec 64) :
    pkmHeadersAt a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen ∗
      Live ∗ Pool ∗ stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ c3) ⊢
    Pool ∗ Live ∗ stackAt sp extHookStack ∗
      (memRegion a 248 ∗ memRegion (sp - 16416#64) 32) := by
  have hh := pkmHeadersAt_entails_memRegion_248
    a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen
  have hs := cells4_entails_stack_bottomX_placed sp fp lr x19 c3
  have hgroup :
      pkmHeadersAt a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen ∗
        Live ∗ Pool ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ c3) =
      pkmHeadersAt a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen ∗
        (Live ∗ Pool ∗
          (stackAt (sp - 32#64) extHookStack ∗
            ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
            ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ c3))) := by
    sep_ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono hh (sepConj_mono_right (sepConj_mono_right hs))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

private theorem pkm_tail_dealloc_post_weaken_placed (a : BitVec 64) (Pool : SepProp) (sp : BitVec 64) :
    Pool ∗ stackAt sp extHookStack ∗ (memRegion a 248 ∗ memRegion (sp - 16416#64) 32) ⊢
      memRegion a 248 ∗ Pool ∗ stackAt sp (32 + extHookStack) := by
  rw [stackAt_pkm_split_placed sp, ← tail_stack_32_from_bottomX_placed sp]
  exact Entails.of_eq (by sep_ac_rfl)

@[reducible]
private def Saved32PreservedPkmPlaced (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x20 = s0.readReg64 .x20 ∧
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem seq_cleanX_pkm_placed [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State} {P : SepProp} {P_mid : State → SepProp}
    {Q : State → Prop} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post := by
  refine sepWP_seq_lscro hcrl (SepWP.mono h1 ?_)
  intro sm Pm hpc hrun ⟨hent, hQ⟩ hcrl_m
  exact SepWP.weaken_pre hent (h2 sm hpc hrun hcrl_m hQ)

private def dropPreKeyMsgFreePoolSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × PreKeyMsgGhost × PreKeySignalMessage) × M.σ) where
  pre := fun ((a, g, m), st) s =>
    ⌜s.readReg64 .x0 = a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗ preKeyMsgAt A.repAlloc g a m ∗
      A.pool lim st s ∗ stackAt s.sp (32 + extHookStack)
  post := fun ((a, _, _), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion a 248 ∗
      freeOnlyPool A lim st sf ∗ stackAt s0.sp (32 + extHookStack)

def dropPreKeyMsgExactSpecPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × PreKeyMsgGhost × PreKeySignalMessage) × M.σ) :=
  withLsCodeRoLoaded lsmpl { dropPreKeyMsgExactSpec M A lim with
    pre := fun ((a, g, m), st) s =>
      ⌜s.readReg64 .x0 = a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗ preKeyMsgAt A.repAlloc g a m ∗
        A.pool lim st s ∗ stackAt s.sp (32 + extHookStack) }

set_option maxHeartbeats 1600000 in
private theorem dropPreKeyMsgFreePool_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_555 H) (blkPl_555).base
      (withLsCodeRoLoaded lsmpl (dropPreKeyMsgFreePoolSpec M A lim)) := by
  unfold withLsCodeRoLoaded dropPreKeyMsgFreePoolSpec
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_555 H) hA
  clear hA
  dsimp only [withLsCodeRoLoaded, lsProg_555, RustCliAllocBudget.live, ↓reduceIte] at hdealloc ⊢
  wp_init x s0
  rcases x with ⟨⟨a, g, m⟩, st⟩
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  subst ‹s0.readReg64 _ = a›
  set a0 := s0.readReg64 (Reg.gpr 0#5)
  set ctLen := BitVec.ofNat 64 m.message.ciphertext.length
  set mserLen := BitVec.ofNat 64 m.message.serialized.length
  set serLen := BitVec.ofNat 64 m.serialized.length
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 32#64 (by assumption)
  nth_rw 1 [stackAt_pkm_split_placed s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i c0 c1 c2 c3
  refine SepWP.weaken_pre
    (sepConj_mono (preKeyMsgAt_entails_deallocX A.repAlloc g a0 m)
      (sepConj_mono_left (freeOnlyPool_intro_nil A lim st s0))) ?_
  wp_pull_exists
  rename_i adPtr adLen kPtr kLen
  let Hdrs : SepProp :=
    pkmHeadersAt a0 g.msg.pqCap g.msg.pqPtr g.msg.ctPtr ctLen g.msg.serPtr mserLen
      adPtr adLen g.serPtr serLen kPtr kLen
  let SavedSlots : SepProp :=
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ c3)
  refine seq_cleanX_pkm_placed
    (mid := (blkPl_555).base +
      (reloc_call_off% (blkLib_555).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 0 + 4#64))
    (P_mid := fun sm => sliceDeallocX A.repAlloc g.msg.ctPtr ctLen ∗
      sliceDeallocX A.repAlloc g.msg.pqPtr g.msg.pqCap ∗
      optSliceDeallocX A.repAlloc adPtr adLen ∗
      sliceDeallocX A.repAlloc g.msg.serPtr mserLen ∗
      sliceDeallocX A.repAlloc g.serPtr serLen ∗
      Hdrs ∗ freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 32#64) extHookStack ∗ SavedSlots)
    (Q := fun sm => Saved32PreservedPkmPlaced s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a0)
    hcrl0 ?_ ?_
  · dsimp only [Hdrs, SavedSlots, pkmHeadersAt]
    conv => arg 4; dsimp only [freeOnlyPool]
    wp_pull_exists; rename_i evs0
    refine SepWP.focus_pure (by sep_focus) fun hevs0 => ?_
    rw [optSliceDeallocX_eq_placed]
    by_cases hk1 : (kPtr == 0#64) = true
    · simp only [hk1, ↓reduceIte, emp_sepConj]
      wp_steps_sync_pool ((blkPl_555).base +
        (reloc_call_off% (blkLib_555).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 0 + 4#64))
      apply SepWP.fold (freeOnlyPool_keep A lim st _ evs0 hevs0) (by sep_focus)
      wp_done
    · simp only [hk1, Bool.false_eq_true, ↓reduceIte]
      rw [sliceDeallocX_eq_placed]
      by_cases hk2 : (kLen == 0#64) = true
      · simp only [hk2, ↓reduceIte, emp_sepConj]
        wp_steps_sync_pool ((blkPl_555).base +
          (reloc_call_off% (blkLib_555).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 0 + 4#64))
        apply SepWP.fold (freeOnlyPool_keep A lim st _ evs0 hevs0) (by sep_focus)
        wp_done
      · simp only [hk2, Bool.false_eq_true, ↓reduceIte]
        rw [sepConj_assoc]
        refine SepWP.pure_elim fun ⟨hpos, hlt⟩ => ?_
        have hrlay : RustLayoutOk kLen.toNat 1 := ⟨⟨hpos, hpow1, by omega⟩, hal1⟩
        apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
        wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        rintro ⟨hcl_c0, hro_c0⟩
        wp_call hdealloc (kPtr, kLen.toNat, 1, M.stepEvents evs0 st)
        apply SepWP.fold (freeOnlyPool_step_dealloc A lim st _ evs0 hevs0 kLen.toNat 1) (by sep_focus)
        wp_done
  · intro s1 hpc1 hrun1 hcrl1
      ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_cleanX_pkm_placed
      (mid := (blkPl_555).base +
        (reloc_call_off% (blkLib_555).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 1 + 4#64))
      (P_mid := fun sm => sliceDeallocX A.repAlloc g.msg.pqPtr g.msg.pqCap ∗
        optSliceDeallocX A.repAlloc adPtr adLen ∗
        sliceDeallocX A.repAlloc g.msg.serPtr mserLen ∗
        sliceDeallocX A.repAlloc g.serPtr serLen ∗
        Hdrs ∗ freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 32#64) extHookStack ∗ SavedSlots)
      (Q := fun sm => Saved32PreservedPkmPlaced s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a0)
      hcrl1 ?_ ?_
    · dsimp only [Hdrs, pkmHeadersAt]
      conv => arg 4; dsimp only [freeOnlyPool]
      wp_pull_exists; rename_i evs1
      refine SepWP.focus_pure (by sep_focus) fun hevs1 => ?_
      rw [sliceDeallocX_eq_placed]
      by_cases hct : (ctLen == 0#64) = true
      · simp only [hct, ↓reduceIte, emp_sepConj]
        wp_steps_sync_pool ((blkPl_555).base +
          (reloc_call_off% (blkLib_555).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 1 + 4#64))
        apply SepWP.fold (freeOnlyPool_keep A lim st _ evs1 hevs1) (by sep_focus)
        wp_done
      · simp only [hct, Bool.false_eq_true, ↓reduceIte]
        rw [sepConj_assoc]
        refine SepWP.pure_elim fun ⟨hpos, hlt⟩ => ?_
        have hrlay : RustLayoutOk ctLen.toNat 1 := ⟨⟨hpos, hpow1, by omega⟩, hal1⟩
        apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl1
        wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        rintro ⟨hcl_c1, hro_c1⟩
        wp_call hdealloc (g.msg.ctPtr, ctLen.toNat, 1, M.stepEvents evs1 st)
        try rw [hsp_1]
        apply SepWP.fold (freeOnlyPool_step_dealloc A lim st _ evs1 hevs1 ctLen.toNat 1) (by sep_focus)
        wp_done
    · intro s2 hpc2 hrun2 hcrl2
        ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_cleanX_pkm_placed
        (mid := (blkPl_555).base +
          (reloc_call_off% (blkLib_555).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 2 + 4#64))
        (P_mid := fun sm => optSliceDeallocX A.repAlloc adPtr adLen ∗
          sliceDeallocX A.repAlloc g.msg.serPtr mserLen ∗
          sliceDeallocX A.repAlloc g.serPtr serLen ∗
          Hdrs ∗ freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 32#64) extHookStack ∗ SavedSlots)
        (Q := fun sm => Saved32PreservedPkmPlaced s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a0)
        hcrl2 ?_ ?_
      · dsimp only [Hdrs, pkmHeadersAt]
        conv => arg 4; dsimp only [freeOnlyPool]
        wp_pull_exists; rename_i evs2
        refine SepWP.focus_pure (by sep_focus) fun hevs2 => ?_
        rw [sliceDeallocX_eq_placed]
        by_cases hpq : (g.msg.pqCap == 0#64) = true
        · simp only [hpq, ↓reduceIte, emp_sepConj]
          wp_steps_sync_pool ((blkPl_555).base +
            (reloc_call_off% (blkLib_555).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 2 + 4#64))
          apply SepWP.fold (freeOnlyPool_keep A lim st _ evs2 hevs2) (by sep_focus)
          wp_done
        · simp only [hpq, Bool.false_eq_true, ↓reduceIte]
          rw [sepConj_assoc]
          refine SepWP.pure_elim fun ⟨hpos, hlt⟩ => ?_
          have hrlay : RustLayoutOk g.msg.pqCap.toNat 1 := ⟨⟨hpos, hpow1, by omega⟩, hal1⟩
          apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl2
          wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl_c2, hro_c2⟩
          wp_call hdealloc (g.msg.pqPtr, g.msg.pqCap.toNat, 1, M.stepEvents evs2 st)
          try rw [hsp_2]
          apply SepWP.fold (freeOnlyPool_step_dealloc A lim st _ evs2 hevs2 g.msg.pqCap.toNat 1) (by sep_focus)
          wp_done
      · intro s3 hpc3 hrun3 hcrl3
          ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_cleanX_pkm_placed
          (mid := (blkPl_555).base +
            (reloc_call_off% (blkLib_555).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 3 + 4#64))
          (P_mid := fun sm => sliceDeallocX A.repAlloc g.msg.serPtr mserLen ∗
            sliceDeallocX A.repAlloc g.serPtr serLen ∗
            Hdrs ∗ freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 32#64) extHookStack ∗ SavedSlots)
          (Q := fun sm => Saved32PreservedPkmPlaced s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a0)
          hcrl3 ?_ ?_
        · dsimp only [Hdrs, pkmHeadersAt]
          conv => arg 4; dsimp only [freeOnlyPool]
          wp_pull_exists; rename_i evs3
          refine SepWP.focus_pure (by sep_focus) fun hevs3 => ?_
          rw [optSliceDeallocX_eq_placed]
          by_cases had1 : (adPtr == 0#64) = true
          · simp only [had1, ↓reduceIte, emp_sepConj]
            wp_steps_sync_pool ((blkPl_555).base +
              (reloc_call_off% (blkLib_555).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 3 + 4#64))
            apply SepWP.fold (freeOnlyPool_keep A lim st _ evs3 hevs3) (by sep_focus)
            wp_done
          · simp only [had1, Bool.false_eq_true, ↓reduceIte]
            rw [sliceDeallocX_eq_placed]
            by_cases had2 : (adLen == 0#64) = true
            · simp only [had2, ↓reduceIte, emp_sepConj]
              wp_steps_sync_pool ((blkPl_555).base +
                (reloc_call_off% (blkLib_555).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 3 + 4#64))
              apply SepWP.fold (freeOnlyPool_keep A lim st _ evs3 hevs3) (by sep_focus)
              wp_done
            · simp only [had2, Bool.false_eq_true, ↓reduceIte]
              rw [sepConj_assoc]
              refine SepWP.pure_elim fun ⟨hpos, hlt⟩ => ?_
              have hrlay : RustLayoutOk adLen.toNat 1 := ⟨⟨hpos, hpow1, by omega⟩, hal1⟩
              apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl3
              wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              rintro ⟨hcl_c3, hro_c3⟩
              wp_call hdealloc (adPtr, adLen.toNat, 1, M.stepEvents evs3 st)
              try rw [hsp_3]
              apply SepWP.fold (freeOnlyPool_step_dealloc A lim st _ evs3 hevs3 adLen.toNat 1) (by sep_focus)
              wp_done
        · intro s4 hpc4 hrun4 hcrl4
            ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          refine seq_cleanX_pkm_placed
            (mid := (blkPl_555).base +
              (reloc_call_off% (blkLib_555).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 4 + 4#64))
            (P_mid := fun sm => sliceDeallocX A.repAlloc g.serPtr serLen ∗
              Hdrs ∗ freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 32#64) extHookStack ∗ SavedSlots)
            (Q := fun sm => Saved32PreservedPkmPlaced s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a0)
            hcrl4 ?_ ?_
          · dsimp only [Hdrs, pkmHeadersAt]
            conv => arg 4; dsimp only [freeOnlyPool]
            wp_pull_exists; rename_i evs4
            refine SepWP.focus_pure (by sep_focus) fun hevs4 => ?_
            rw [sliceDeallocX_eq_placed]
            by_cases hmser : (mserLen == 0#64) = true
            · simp only [hmser, ↓reduceIte, emp_sepConj]
              wp_steps_sync_pool ((blkPl_555).base +
                (reloc_call_off% (blkLib_555).text.relocs "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" 4 + 4#64))
              apply SepWP.fold (freeOnlyPool_keep A lim st _ evs4 hevs4) (by sep_focus)
              wp_done
            · simp only [hmser, Bool.false_eq_true, ↓reduceIte]
              rw [sepConj_assoc]
              refine SepWP.pure_elim fun ⟨hpos, hlt⟩ => ?_
              have hrlay : RustLayoutOk mserLen.toNat 1 := ⟨⟨hpos, hpow1, by omega⟩, hal1⟩
              apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl4
              wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              rintro ⟨hcl_c4, hro_c4⟩
              wp_call hdealloc (g.msg.serPtr, mserLen.toNat, 1, M.stepEvents evs4 st)
              try rw [hsp_4]
              apply SepWP.fold (freeOnlyPool_step_dealloc A lim st _ evs4 hevs4 mserLen.toNat 1) (by sep_focus)
              wp_done
          · intro s5 hpc5 hrun5 hcrl5
              ⟨⟨hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
            conv => arg 4; dsimp only [Hdrs, SavedSlots, pkmHeadersAt, freeOnlyPool]
            wp_pull_exists; rename_i evs5
            refine SepWP.focus_pure (by sep_focus) fun hevs5 => ?_
            rw [sliceDeallocX_eq_placed]
            by_cases hser : (serLen == 0#64) = true
            · simp only [hser, ↓reduceIte, emp_sepConj]
              wp_steps_sync_pool (s0.readReg64 .lr)
              refine SepWP.weaken_pre
                (Entails.trans
                  (Entails.of_eq (by dsimp only [pkmHeadersAt]; sep_ac_rfl))
                  (pkm_empty_epilogue_weaken_placed a0 g.msg.pqCap g.msg.pqPtr g.msg.ctPtr ctLen
                    g.msg.serPtr mserLen adPtr adLen g.serPtr serLen kPtr kLen
                    _ s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) c3)) ?_
              apply SepWP.fold (freeOnlyPool_keep A lim st _ evs5 hevs5) (by sep_focus)
              wp_done
            · simp only [hser, Bool.false_eq_true, ↓reduceIte]
              rw [sepConj_assoc]
              refine SepWP.pure_elim fun ⟨hpos, hlt⟩ => ?_
              have hrlay : RustLayoutOk serLen.toNat 1 := ⟨⟨hpos, hpow1, by omega⟩, hal1⟩
              apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl5
              wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
              refine SepWP.weaken_pre
                (Entails.trans
                  (Entails.of_eq (by dsimp only [pkmHeadersAt]; sep_ac_rfl))
                  (pkm_tail_dealloc_pre_weaken_placed a0 g.msg.pqCap g.msg.pqPtr g.msg.ctPtr ctLen
                    g.msg.serPtr mserLen adPtr adLen g.serPtr serLen kPtr kLen
                    (A.repAlloc.live g.serPtr serLen.toNat 1 ∗ memRegion g.serPtr serLen.toNat)
                    _ s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) c3)) ?_
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              rintro ⟨hcl_tail, hro_tail⟩
              wp_call hdealloc (g.serPtr, serLen.toNat, 1, M.stepEvents evs5 st)
              apply SepWP.fold (freeOnlyPool_step_dealloc A lim st _ evs5 hevs5 serLen.toNat 1) (by sep_focus)
              refine SepWP.weaken_pre
                (Entails.trans
                  (Entails.of_eq (by sep_ac_rfl))
                  (pkm_tail_dealloc_post_weaken_placed a0 _ s0.sp)) ?_
              wp_done

theorem dropPreKeyMsgExact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_555 H) (blkPl_555).base
      (dropPreKeyMsgExactSpecPlaced M A lim) := by
  refine subroutine_ok_map_frame_weaken id (fun _ _ => emp)
    (dropPreKeyMsgFreePool_placed_ok hA) ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, g, m⟩, st⟩ s0
    dsimp only [dropPreKeyMsgExactSpecPlaced, withLsCodeRoLoaded,
      dropPreKeyMsgExactSpec, dropPreKeyMsgFreePoolSpec, id]
    rw [sepConj_emp]
    exact Entails.refl _
  · rintro ⟨⟨a, g, m⟩, st⟩ s0 sf
    dsimp only [dropPreKeyMsgExactSpecPlaced, withLsCodeRoLoaded,
      dropPreKeyMsgExactSpec, dropPreKeyMsgFreePoolSpec, freeOnlyPool, id]
    rw [sepConj_emp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro evs
    refine Entails.sepExists_right evs ?_
    have hord :
        ⌜sf.trace = s0.trace⌝ ∗ memRegion a 248 ∗
          (⌜∀ ev ∈ evs, ∃ al sz, ev = .free al sz⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp (32 + extHookStack) =
        ⌜sf.trace = s0.trace⌝ ∗ (⌜∀ ev ∈ evs, ∃ al sz, ev = .free al sz⌝ ∗
          (memRegion a 248 ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (32 + extHookStack))) := by
      sep_ac_rfl
    rw [hord]
    apply Entails.pure_left; intro htr
    apply Entails.pure_left; intro hevs
    exact Entails.pure_right ⟨htr, hevs⟩ (Entails.refl _)
  · intro _ _ _
    dsimp only [dropPreKeyMsgExactSpecPlaced, withLsCodeRoLoaded]
    exact Entails.pure_left False.elim
  · intros; rfl

end DropPreKeyMsgPlacedBudgetHelpers

/-- Proves the budget-threaded `dropPreKeyMsgSpecPlaced` contract at stack budgets `32 + extHookStack ≤ stk ≤ 2 ^ 64`. -/
theorem cliDropPreKeyMsg_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_555 H) (blkPl_555).base
      (dropPreKeyMsgSpecPlaced M A lim stk) := by
  refine subroutine_ok_map_frame_weaken
    (fun (x, st) => ((x.a, x.g, x.m), st))
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (32 + extHookStack)))
    (dropPreKeyMsgExact_placed_ok hA) ?_ ?_ ?_ ?_
  · rintro ⟨x, st⟩ s0
    dsimp only [dropPreKeyMsgSpecPlaced, dropPreKeyMsgExactSpecPlaced,
      withLsCodeRoLoaded, dropPreKeyMsgSpec, dropPreKeyMsgExactSpec]
    have hsplit : stackAt s0.sp stk =
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (32 + extHookStack)) ∗
          stackAt s0.sp (32 + extHookStack) := by
      have h := ProofLib.stackAt_split_bottom s0.sp (32 + extHookStack) (stk - (32 + extHookStack)) (by omega)
      rwa [Nat.add_sub_of_le hstk] at h
    rw [hsplit]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨x, st⟩ s0 sf
    dsimp only [dropPreKeyMsgSpecPlaced, dropPreKeyMsgExactSpecPlaced,
      withLsCodeRoLoaded, dropPreKeyMsgSpec, dropPreKeyMsgExactSpec]
    have hsplit : stackAt s0.sp stk =
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (32 + extHookStack)) ∗
          stackAt s0.sp (32 + extHookStack) := by
      have h := ProofLib.stackAt_split_bottom s0.sp (32 + extHookStack) (stk - (32 + extHookStack)) (by omega)
      rwa [Nat.add_sub_of_le hstk] at h
    rw [hsplit, sepExists_sepConj_left]
    exact Entails.sepExists_mono fun _ => Entails.of_eq (by sep_ac_rfl)
  · intro _ _ _
    dsimp only [dropPreKeyMsgSpecPlaced, dropPreKeyMsgExactSpecPlaced, withLsCodeRoLoaded]
    exact Entails.pure_left False.elim
  · intros; rfl

/-- Transfers `cliDropPreKeyMsg_placed_ok` to any caller block `i < 619`. -/
theorem cliDropPreKeyMsg_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [hcaller : IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A lim H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_555).base
      (dropPreKeyMsgSpecPlaced M A lim stk) := by
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg (lsProg_555 H) i 555 H
    hcaller (instIsLsBlockProg_555 H) (blkPl_555).base _
    (cliDropPreKeyMsg_placed_ok hA stk hstk hstk64)
    _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsgPlacedBudget
