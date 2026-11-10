/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.Pure

/-!
# Budget-Threaded Relocatable `IdentityFiles` Drop Glue and Directory Loop Helpers

Defines `dropStoresSpecPlaced` and `dropDirPairSpecPlaced` over `RustCliAllocBudget M`, proves
inline directory-drop loop helpers, and establishes `cliDropIdentityFiles_placed_ok` on block `549`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc arrayAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded
)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (dirAt dirEntryAt)
open CryptoVerification.SignalSession.Cli.MainHops (storesAt)
open CryptoVerification.SignalSession.Cli.Placed (
  blkLib_549 blkLib_550 blkPl_549 blkPl_550 lsProg_549 lsProg_550
)
open CryptoVerification.SignalSession.Cli.Put.Helpers (stackAt_sub_split)
open CryptoVerification.SignalSession.Cli.RunProofs (DropDirPairGhost DropStoresGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.Helpers (
  Saved48Preserved add_32_add_48 add_32_neg_24 add_32_neg_24_assoc add_32_neg_32
  add_32_neg_32_assoc add_32_neg_8 add_32_neg_8_assoc add_32_sub_24 add_32_sub_24_assoc
  add_32_sub_32 add_32_sub_32_assoc add_32_sub_8 add_32_sub_8_assoc add_one_sub_one
  cons_len_mul_48 dirEntryAt_expose dirRawAt dirRawAt_expose dirRawAt_expose_off entryHeadersAt
  entryHeadersAt_entails_memRegion_48 exists_two_pow_eight exists_two_pow_one idExactStk
  id_cap0_ret_weaken id_entry_raw_ro id_tail_dealloc_post id_tail_dealloc_pre_weaken
  mul_48_reg ofNat_add_one_beq_one_false ofNat_beq_zero_false ofNat_succ_eq_add_one
  pos_of_beq_zero_false post_dir_loop_weaken post_dir_loop_weaken_off reg_fp_eq reg_lr_eq
  reg_x0_eq reg_x19_eq reg_x1_eq reg_x20_eq reg_x21_eq reg_x22_eq reg_x23_eq reg_x24_eq
  reg_x25_eq reg_x26_eq reg_x27_eq reg_x28_eq reg_x2_eq roPathAt sep_pull_entry
  sep_push_entry sep_rejoin_entries stackAt_id_split storesExactStk
  sub_24_of_add_32 sub_32_of_add_32 sub_8_of_add_32 tail_len_mul_48_lt vecPinDeallocX
  weaken_perm word_and_32_rest_entails_40 word_and_32_rest_entails_40_off
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget RustLayoutOk
  rustDeallocEvents
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresBudget (
  dropDirPairSpec dropStoresSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (dealloc_lscro_of_cli)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

/-- Budget-threaded `[LibsignalPlacement]` specification for `drop_glue::<Stores>` (block `550`). -/
def dropStoresSpecPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (DropStoresGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl { dropStoresSpec M A lim stk with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗ storesAt A.repAlloc x.a x.g ∗
        A.pool lim st s ∗ stackAt s.sp stk }

/-- Budget-threaded `[LibsignalPlacement]` specification for `drop_glue::<IdentityFiles>` (block `549`). -/
def dropDirPairSpecPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (DropDirPairGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl { dropDirPairSpec M A lim stk with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
        dirAt A.repAlloc x.a x.d0 ∗ dirAt A.repAlloc (x.a + 0x28#64) x.d1 ∗
        A.pool lim st s ∗ stackAt s.sp stk }

def freeOnlyPool {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent,
    ⌜∀ ev ∈ evs, ∃ al sz, ev = .free al sz⌝ ∗ A.pool lim (M.stepEvents evs st) s

theorem freeOnlyPool_intro_nil {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ freeOnlyPool A lim st s := by
  unfold freeOnlyPool
  refine Entails.sepExists_right [] ?_
  rw [M.stepEvents_nil]
  exact Entails.pure_right (by intro _ h; cases h) (Entails.refl _)

theorem freeOnlyPool_keep {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (evs : List AllocEvent)
    (hevs : ∀ ev ∈ evs, ∃ al sz, ev = .free al sz) :
    A.pool lim (M.stepEvents evs st) s ⊢ freeOnlyPool A lim st s := by
  unfold freeOnlyPool
  exact Entails.sepExists_right evs (Entails.pure_right hevs (Entails.refl _))

theorem freeOnlyPool_step_dealloc {M : AllocCostModel} (A : RustCliAllocBudget M)
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

theorem freeOnlyPool_step_evs {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (evs₁ evs₂ : List AllocEvent)
    (h1 : ∀ ev ∈ evs₁, ∃ al sz, ev = .free al sz)
    (h2 : ∀ ev ∈ evs₂, ∃ al sz, ev = .free al sz) :
    A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s ⊢
      freeOnlyPool A lim st s := by
  unfold freeOnlyPool
  refine Entails.sepExists_right (evs₁ ++ evs₂) ?_
  rw [M.stepEvents_append]
  refine Entails.pure_right ?_ (Entails.refl _)
  intro ev hmem
  rcases List.mem_append.mp hmem with hm1 | hm2
  · exact h1 ev hm1
  · exact h2 ev hm2

theorem sepWP_let_state {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (h : ∀ sc : State, sc = s → SepWP prog target s P post) :
    SepWP prog target s P post :=
  h s rfl

section DropStoresPlacedBudgetHelpers

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] exists_two_pow_one exists_two_pow_eight
attribute [local wp_norm, local arm64_norm]
  sub_32_of_add_32 sub_24_of_add_32 sub_8_of_add_32
  add_32_sub_32 add_32_sub_32_assoc add_32_sub_24 add_32_sub_24_assoc
  add_32_sub_8 add_32_sub_8_assoc
  add_32_neg_32 add_32_neg_32_assoc add_32_neg_24 add_32_neg_24_assoc
  add_32_neg_8 add_32_neg_8_assoc add_one_sub_one
attribute [local simp, local wp_norm, local arm64_norm]
  reg_x0_eq reg_x1_eq reg_x2_eq reg_x19_eq reg_x20_eq reg_x21_eq reg_x22_eq
  reg_x23_eq reg_x24_eq reg_x25_eq reg_x26_eq reg_x27_eq reg_x28_eq
  reg_fp_eq reg_lr_eq

theorem seq_cleanX_placed [LibsignalPlacement] {prog : Program}
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

set_option hygiene false in
local macro "prove_dir_loop_placed" bodyId:ident loopId:ident
    blkProgId:ident blkPlId:ident blkLibId:ident
    bLoopIdx:num bCondIdx:num blDeallocIdx:num bExitIdx:num : command => `(
  set_option maxHeartbeats 1600000 in
  theorem $bodyId [LibsignalPlacement]
      {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
      (hA : AllocContractsXCliPlaced A lim H)
      (st : M.σ) (s0 : State) (fsp p0 ptr : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
      ∀ (cur cnt : BitVec 64) (e : List (BitVec 8) × List (BitVec 8))
        (s : State) (Frame : SepProp),
        s.pc = ($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b.cond" $bCondIdx + 4#64) →
        s.status = .Running →
        LibsignalCodeRoLoaded lsmpl s.mem →
        Saved48Preserved s0 s fsp →
        s.readReg64 (Reg.gpr 19#5) = p0 →
        s.readReg64 (Reg.gpr 20#5) = ptr →
        s.readReg64 (Reg.gpr 21#5) = cnt →
        s.readReg64 (Reg.gpr 22#5) = cur + 32#64 →
        SepWP ($blkProgId H)
          (($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b" $bLoopIdx + 4#64))
          s
          (dirEntryAt A.repAlloc e cur ∗ freeOnlyPool A lim st s ∗ stackAt fsp extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur 48 ∗ freeOnlyPool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 (Reg.gpr 19#5) = p0 ∧
            sm.readReg64 (Reg.gpr 20#5) = ptr ∧
            sm.readReg64 (Reg.gpr 21#5) = cnt ∧
            sm.readReg64 (Reg.gpr 22#5) = cur + 32#64) := by
    have hdealloc := dealloc_lscro_of_cli (callerProg := $blkProgId H) hA
    clear hA
    dsimp only [withLsCodeRoLoaded, $blkProgId:ident, RustCliAllocBudget.live, ↓reduceIte]
      at hdealloc ⊢
    intro cur cnt e s Frame hpc hrun hcrl hpres hx19 hx20 hx21 hx22
    rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
    refine SepWP.weaken_pre (sepConj_mono_left (dirEntryAt_expose A.repAlloc e cur)) ?_
    wp_pull_exists
    rename_i nc np bc bp
    refine seq_cleanX_placed
      (mid := ($blkPlId).base + (words_insn_off% ($blkLibId).text.code "bl" $blDeallocIdx + 4#64))
      (P_mid := fun sm => (entryHeadersAt cur nc np bc bp ∗ vecPinDeallocX A.repAlloc bc bp) ∗
        freeOnlyPool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 (Reg.gpr 19#5) = p0 ∧ sm.readReg64 (Reg.gpr 20#5) = ptr ∧
        sm.readReg64 (Reg.gpr 21#5) = cnt ∧ sm.readReg64 (Reg.gpr 22#5) = cur + 32#64)
      hcrl ?_ ?_
    · nth_rw 1 [show vecPinDeallocX A.repAlloc nc np =
          if (nc == 0#64) = true then emp
          else ⌜0 < nc.toNat ∧ nc.toNat < 2 ^ 63⌝ ∗ A.repAlloc.live np nc.toNat 1 ∗ memRegion np nc.toNat
          from rfl]
      dsimp only [entryHeadersAt]
      conv => arg 4; dsimp only [freeOnlyPool]
      wp_pull_exists; rename_i evs0
      refine SepWP.focus_pure (by sep_focus) fun hevs0 => ?_
      by_cases hnc : (nc == 0#64) = true <;>
        simp only [hnc, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps_sync_pool
          (($blkPlId).base + (words_insn_off% ($blkLibId).text.code "bl" $blDeallocIdx + 4#64))
        apply SepWP.fold (freeOnlyPool_keep A lim st _ evs0 hevs0) (by sep_focus)
        try wp_done
      · refine SepWP.weaken_pre (Entails.of_eq (show _ =
          ⌜0 < nc.toNat ∧ nc.toNat < 2 ^ 63⌝ ∗
            ((cur ↦₆₄ nc) ∗ ((cur + 8#64) ↦₆₄ np) ∗ memRegion (cur + 16#64) 8 ∗
              ((cur + 24#64) ↦₆₄ bc) ∗ ((cur + 32#64) ↦₆₄ bp) ∗ memRegion (cur + 40#64) 8 ∗
              A.repAlloc.live np nc.toNat 1 ∗ memRegion np nc.toNat ∗ vecPinDeallocX A.repAlloc bc bp ∗
              A.pool lim (M.stepEvents evs0 st) s ∗ stackAt fsp extHookStack ∗ Frame) by sep_ac_rfl)) ?_
        refine SepWP.pure_elim ?_
        rintro ⟨hpos, hlt⟩
        apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
        wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_c1
        have ⟨hcl_c1, hro_c1⟩ := hcrl_c1
        have hrlay : RustLayoutOk nc.toNat 1 := ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩
        wp_call hdealloc (np, nc.toNat, 1, M.stepEvents evs0 st)
        try rw [hsp]
        apply SepWP.fold (freeOnlyPool_step_dealloc A lim st _ evs0 hevs0 nc.toNat 1) (by sep_focus)
        try wp_done
    · intro s1 hpc1 hrun1 hcrl1
        ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩,
          hx19_1, hx20_1, hx21_1, hx22_1⟩
      have hstep2 : SepWP ($blkProgId H)
          (($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b" $bLoopIdx + 4#64)) s1
          ((entryHeadersAt cur nc np bc bp ∗ vecPinDeallocX A.repAlloc bc bp) ∗
            freeOnlyPool A lim st s1 ∗ stackAt fsp extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ entryHeadersAt cur nc np bc bp ∗ freeOnlyPool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 (Reg.gpr 19#5) = p0 ∧
            sm.readReg64 (Reg.gpr 20#5) = ptr ∧
            sm.readReg64 (Reg.gpr 21#5) = cnt ∧
            sm.readReg64 (Reg.gpr 22#5) = cur + 32#64) := by
        dsimp only [$blkProgId:ident, ↓reduceIte, entryHeadersAt, vecPinDeallocX]
        conv => arg 4; dsimp only [freeOnlyPool]
        wp_pull_exists; rename_i evs1
        refine SepWP.focus_pure (by sep_focus) fun hevs1 => ?_
        by_cases hbc : (bc == 0#64) = true <;>
          simp only [hbc, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps_sync_pool
            (($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b" $bLoopIdx + 4#64))
          apply SepWP.fold (freeOnlyPool_keep A lim st _ evs1 hevs1) (by sep_focus)
          try wp_done
        · refine SepWP.weaken_pre (Entails.of_eq (show _ =
            ⌜0 < bc.toNat ∧ bc.toNat < 2 ^ 63⌝ ∗
              ((cur ↦₆₄ nc) ∗ ((cur + 8#64) ↦₆₄ np) ∗ memRegion (cur + 16#64) 8 ∗
                ((cur + 24#64) ↦₆₄ bc) ∗ ((cur + 32#64) ↦₆₄ bp) ∗ memRegion (cur + 40#64) 8 ∗
                A.repAlloc.live bp bc.toNat 1 ∗ memRegion bp bc.toNat ∗
                A.pool lim (M.stepEvents evs1 st) s1 ∗ stackAt fsp extHookStack ∗ Frame) by sep_ac_rfl)) ?_
          refine SepWP.pure_elim ?_
          rintro ⟨hpos, hlt⟩
          apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl1
          wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro hcrl_c2
          have ⟨hcl_c2, hro_c2⟩ := hcrl_c2
          have hrlay : RustLayoutOk bc.toNat 1 := ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩
          wp_call hdealloc (bp, bc.toNat, 1, M.stepEvents evs1 st)
          wp_steps_sync_pool
            (($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b" $bLoopIdx + 4#64))
          try rw [hsp_1]
          apply SepWP.fold (freeOnlyPool_step_dealloc A lim st _ evs1 hevs1 bc.toNat 1) (by sep_focus)
          try wp_done
      exact SepWP.mono hstep2 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (entryHeadersAt_entails_memRegion_48 cur nc np bc bp)),
          h.2⟩)

  set_option maxHeartbeats 1600000 in
  theorem $loopId [LibsignalPlacement]
      {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
      (hA : AllocContractsXCliPlaced A lim H)
      (st : M.σ) (s0 : State) (fsp p0 ptr : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
      ∀ (rest : List (List (BitVec 8) × List (BitVec 8))) (cur : BitVec 64)
        (s : State) (Frame : SepProp),
        rest ≠ [] →
        rest.length * 48 < 2 ^ 63 →
        s.pc = ($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b.cond" $bCondIdx + 4#64) →
        s.status = .Running →
        LibsignalCodeRoLoaded lsmpl s.mem →
        Saved48Preserved s0 s fsp →
        s.readReg64 (Reg.gpr 19#5) = p0 →
        s.readReg64 (Reg.gpr 20#5) = ptr →
        s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 rest.length →
        s.readReg64 (Reg.gpr 22#5) = cur + 32#64 →
        SepWP ($blkProgId H)
          (($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b" $bExitIdx + 4#64))
          s
          (arrayAt (dirEntryAt A.repAlloc) 48 cur rest ∗ freeOnlyPool A lim st s ∗ stackAt fsp extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur (rest.length * 48) ∗ freeOnlyPool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 (Reg.gpr 19#5) = p0 ∧
            sm.readReg64 (Reg.gpr 20#5) = ptr) := by
    have hbody := @$bodyId _ M A lim H hA st s0 fsp p0 ptr hfsp_align
    clear hA
    dsimp only [$blkProgId:ident, ↓reduceIte, BitVec.ofNat_eq_ofNat] at hbody ⊢
    intro rest
    induction rest with
    | nil =>
      intro _ _ _ hne
      exact absurd rfl hne
    | cons hd tl ih =>
      intro cur s Frame _ hlen hpc hrun hcrl hpres hx19 hx20 hx21 hx22
      rw [show arrayAt (dirEntryAt A.repAlloc) 48 cur (hd :: tl) =
            dirEntryAt A.repAlloc hd cur ∗ arrayAt (dirEntryAt A.repAlloc) 48 (cur + 48#64) tl from rfl,
          sep_pull_entry]
      refine seq_cleanX_placed
        (mid := ($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b" $bLoopIdx + 4#64))
        (P_mid := fun sm => memRegion cur 48 ∗ freeOnlyPool A lim st sm ∗ stackAt fsp extHookStack ∗
          (arrayAt (dirEntryAt A.repAlloc) 48 (cur + 48#64) tl ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 (Reg.gpr 19#5) = p0 ∧ sm.readReg64 (Reg.gpr 20#5) = ptr ∧
          sm.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (hd :: tl).length ∧
          sm.readReg64 (Reg.gpr 22#5) = cur + 32#64)
        hcrl
        (hbody cur (BitVec.ofNat 64 (hd :: tl).length) hd s
          (arrayAt (dirEntryAt A.repAlloc) 48 (cur + 48#64) tl ∗ Frame)
          hpc hrun hcrl hpres hx19 hx20 hx21 hx22) ?_
      intro s4 hpc4 hrun4 hcrl4 ⟨hpres4, hx19_4, hx20_4, hx21_4, hx22_4⟩
      cases tl with
      | nil =>
        rcases hpres4 with ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
        simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
          BitVec.ofNat_eq_ofNat, arrayAt, emp_sepConj] at hx21_4 ⊢
        conv => arg 4; dsimp only [freeOnlyPool]
        wp_pull_exists; rename_i evs_nil
        refine SepWP.focus_pure (by sep_focus) fun hevs_nil => ?_
        wp_steps_sync_pool (($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b" $bExitIdx + 4#64))
        apply SepWP.fold (freeOnlyPool_keep A lim st _ evs_nil hevs_nil) (by sep_focus)
        try wp_done
      | cons hd2 tl2 =>
        have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
        have htl_len := tail_len_mul_48_lt hlen
        rw [show (hd :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
            ofNat_succ_eq_add_one] at hx21_4
        have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
        refine seq_cleanX_placed
          (mid := ($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b.cond" $bCondIdx + 4#64))
          (P_mid := fun sm => arrayAt (dirEntryAt A.repAlloc) 48 (cur + 48#64) (hd2 :: tl2) ∗
            freeOnlyPool A lim st sm ∗ stackAt fsp extHookStack ∗ (memRegion cur 48 ∗ Frame))
          (Q := fun sm => Saved48Preserved s0 sm fsp ∧
            sm.readReg64 (Reg.gpr 19#5) = p0 ∧ sm.readReg64 (Reg.gpr 20#5) = ptr ∧
            sm.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (hd2 :: tl2).length ∧
            sm.readReg64 (Reg.gpr 22#5) = (cur + 48#64) + 32#64)
          hcrl4 ?_ ?_
        · rcases hpres4 with ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
          rw [sep_push_entry]
          conv => arg 4; dsimp only [freeOnlyPool]
          wp_pull_exists; rename_i evs_c
          refine SepWP.focus_pure (by sep_focus) fun hevs_c => ?_
          wp_steps_sync_pool
            (($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b.cond" $bCondIdx + 4#64))
          rw [add_32_add_48]
          apply SepWP.fold (freeOnlyPool_keep A lim st _ evs_c hevs_c) (by sep_focus)
          try wp_done
        · intro s5 hpc5 hrun5 hcrl5 ⟨hpres5, hx19_5, hx20_5, hx21_5, hx22_5⟩
          refine SepWP.mono
            (ih (cur + 48#64) s5 (memRegion cur 48 ∗ Frame)
              htl_ne htl_len hpc5 hrun5 hcrl5 hpres5 hx19_5 hx20_5 hx21_5 hx22_5) ?_
          intro sf Pf _ _ h
          refine ⟨Entails.trans h.1 ?_, h.2⟩
          have hsplit := cons_len_mul_48 hd (hd2 :: tl2)
          have hbound : 48 + (hd2 :: tl2).length * 48 ≤ 2 ^ 64 := by
            rw [hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
          rw [sep_rejoin_entries, ← hsplit,
              ProofLib.memRegion_split cur 48 ((hd2 :: tl2).length * 48) hbound]
          exact Entails.refl _
)

prove_dir_loop_placed id_loop0_body_placed id_loop0_placed
  lsProg_549 blkPl_549 blkLib_549 0 0 0 1

prove_dir_loop_placed id_loop1_body_placed id_loop1_placed
  lsProg_549 blkPl_549 blkLib_549 2 1 3 3

prove_dir_loop_placed stores_loop0_body_placed stores_loop0_placed
  lsProg_550 blkPl_550 blkLib_550 0 0 1 1

prove_dir_loop_placed stores_loop1_body_placed stores_loop1_placed
  lsProg_550 blkPl_550 blkLib_550 2 1 5 3

prove_dir_loop_placed stores_loop2_body_placed stores_loop2_placed
  lsProg_550 blkPl_550 blkLib_550 4 2 8 5

prove_dir_loop_placed stores_loop3_body_placed stores_loop3_placed
  lsProg_550 blkPl_550 blkLib_550 6 3 11 7

set_option hygiene false in
local macro "prove_dir_nontail_placed" blockId:ident loopId:ident
    off:term:max off8:term:max off16:term:max off24:term:max
    blStartIdx:num bCondIdx:num bExitIdx:num blEndIdx:num : command => `(
  set_option maxHeartbeats 1600000 in
  theorem $blockId [LibsignalPlacement]
      {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
      (hA : AllocContractsXCliPlaced A lim H)
      (st : M.σ) (s0 : State) (fsp p0 : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
      ∀ (xs : List (List (BitVec 8) × List (BitVec 8))) (s : State) (Frame : SepProp),
        s.pc = (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "bl" $blStartIdx + 4#64) →
        s.status = .Running →
        LibsignalCodeRoLoaded lsmpl s.mem →
        Saved48Preserved s0 s fsp →
        s.readReg64 (Reg.gpr 19#5) = p0 →
        SepWP (lsProg_550 H)
          ((blkPl_550).base + (words_insn_off% (blkLib_550).text.code "bl" $blEndIdx + 4#64))
          s
          (dirRawAt A.repAlloc (p0 + $off) xs ∗ freeOnlyPool A lim st s ∗ stackAt fsp extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion (p0 + $off) 40 ∗ freeOnlyPool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 (Reg.gpr 19#5) = p0) := by
    have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_550 H) hA
    have hloop := @$loopId _ M A lim H hA st
    clear hA
    dsimp only [withLsCodeRoLoaded, lsProg_550, RustCliAllocBudget.live, ↓reduceIte,
      BitVec.ofNat_eq_ofNat] at hdealloc hloop ⊢
    intro xs s Frame hpc hrun hcrl hpres hx19
    rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
    have ho8 : (p0 + $off) + 8#64 = p0 + $off8 := by bv_omega
    have ho16 : (p0 + $off) + 16#64 = p0 + $off16 := by bv_omega
    have ho24 : (p0 + $off) + 24#64 = p0 + $off24 := by bv_omega
    refine SepWP.weaken_pre
      (sepConj_mono_left
        (dirRawAt_expose_off A.repAlloc p0 $off $off8 $off16 $off24 ho8 ho16 ho24 xs)) ?_
    wp_pull_exists
    rename_i cap ptr
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ xs.length * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (((p0 + $off) ↦₆₄ cap) ∗
          ((p0 + $off8) ↦₆₄ ptr) ∗
          ((p0 + $off16) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
          arrayAt (dirEntryAt A.repAlloc) 48 ptr xs ∗
          (if cap = 0 then emp
           else A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
             memRegion (ptr + BitVec.ofNat 64 (xs.length * 48)) ((cap.toNat - xs.length) * 48)) ∗
          memRegion (p0 + $off24) 16 ∗
          freeOnlyPool A lim st s ∗ stackAt fsp extHookStack ∗ Frame) by sep_ac_rfl)) ?_
    refine SepWP.pure_elim ?_
    rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
    refine seq_cleanX_placed
      (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "b" $bExitIdx + 4#64))
      (P_mid := fun sm =>
        ((p0 + $off) ↦₆₄ cap) ∗
        ((p0 + $off8) ↦₆₄ ptr) ∗
        ((p0 + $off16) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
        memRegion ptr (xs.length * 48) ∗
        (if cap = 0 then emp
         else A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * 48)) ((cap.toNat - xs.length) * 48)) ∗
        memRegion (p0 + $off24) 16 ∗
        freeOnlyPool A lim st sm ∗ stackAt fsp extHookStack ∗ Frame)
      (Q := fun sm =>
        Saved48Preserved s0 sm fsp ∧
        sm.readReg64 (Reg.gpr 19#5) = p0 ∧
        sm.readReg64 (Reg.gpr 20#5) = ptr)
      hcrl ?_ ?_
    · cases xs with
      | nil =>
        simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
        conv => arg 4; dsimp only [freeOnlyPool]
        wp_pull_exists; rename_i evs_n
        refine SepWP.focus_pure (by sep_focus) fun hevs_n => ?_
        wp_steps_sync_pool
          ((blkPl_550).base + (words_insn_off% (blkLib_550).text.code "b" $bExitIdx + 4#64))
        apply SepWP.fold (freeOnlyPool_keep A lim st _ evs_n hevs_n) (by sep_focus)
        try wp_done
      | cons hd tl =>
        have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) (by omega)
        conv => arg 4; dsimp only [freeOnlyPool]
        wp_pull_exists; rename_i evs_p
        refine SepWP.focus_pure (by sep_focus) fun hevs_p => ?_
        apply sepWP_seq_lscro
          (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "b.cond" $bCondIdx + 4#64))
          hcrl
        wp_steps_sync_pool
          ((blkPl_550).base + (words_insn_off% (blkLib_550).text.code "b.cond" $bCondIdx + 4#64))
        apply SepWP.fold (freeOnlyPool_keep A lim st _ evs_p hevs_p) (by sep_focus)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_p
        refine sepWP_let_state fun sc hsc => ?_
        have hpre_eq :
            (freeOnlyPool A lim st sc ∗
              ((p0 + $off) ↦₆₄ cap) ∗
              ((p0 + $off8) ↦₆₄ ptr) ∗
              ((p0 + $off16) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
              arrayAt (dirEntryAt A.repAlloc) 48 ptr (hd :: tl) ∗
              (if cap = 0 then emp
               else A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
                 memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 48))
                   ((cap.toNat - (hd :: tl).length) * 48)) ∗
              memRegion (p0 + $off24) 16 ∗
              stackAt fsp extHookStack ∗ Frame) =
            (arrayAt (dirEntryAt A.repAlloc) 48 ptr (hd :: tl) ∗
              freeOnlyPool A lim st sc ∗ stackAt fsp extHookStack ∗
              (((p0 + $off) ↦₆₄ cap) ∗
                ((p0 + $off8) ↦₆₄ ptr) ∗
                ((p0 + $off16) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                (if cap = 0 then emp
                 else A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
                   memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 48))
                     ((cap.toNat - (hd :: tl).length) * 48)) ∗
                memRegion (p0 + $off24) 16 ∗ Frame)) := by
          sep_ac_rfl
        subst hsc
        rw [hpre_eq]
        refine SepWP.mono
          (hloop s0 fsp p0 ptr hfsp_align (hd :: tl) ptr _ _
            (List.cons_ne_nil _ _) hlen_lt (by wp_norm_goal) (by wp_norm_lhs) hcrl_p
            ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
            hx19 rfl rfl rfl) ?_
        intro sm Pm _ _ h
        exact ⟨Entails.trans h.1 (Entails.of_eq (by sep_ac_rfl)), h.2⟩
    · intro sm hpcm hrunm hcrlm
        ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx19_m, hx20_m⟩
      refine SepWP.weaken_pre
        (post_dir_loop_weaken_off A.repAlloc p0 $off $off8 $off16 $off24
          cap ptr ho8 ho16 ho24 xs.length hlen_le hcap_lt _) ?_
      conv => arg 4; dsimp only [freeOnlyPool]
      wp_pull_exists; rename_i evs_m
      refine SepWP.focus_pure (by sep_focus) fun hevs_m => ?_
      by_cases hcap : (cap == 0#64) = true <;>
        simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps_sync_pool
          ((blkPl_550).base + (words_insn_off% (blkLib_550).text.code "bl" $blEndIdx + 4#64))
        apply SepWP.fold (freeOnlyPool_keep A lim st _ evs_m hevs_m) (by sep_focus)
        refine sepWP_let_state fun sc hsc => ?_
        refine SepWP.weaken_pre
          (weaken_perm
            (word_and_32_rest_entails_40_off p0 $off $off8 cap ho8
              (freeOnlyPool A lim st sc ∗ stackAt fsp extHookStack ∗ Frame))
            (by subst hsc; sep_ac_rfl)) ?_
        subst hsc
        try wp_done
      · have hcap_pos := pos_of_beq_zero_false hcap
        have hsz_pos : 0 < cap.toNat * 48 := Nat.mul_pos hcap_pos (by decide)
        apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrlm
        wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_cm
        have ⟨hcl_cm, hro_cm⟩ := hcrl_cm
        rw [mul_48_reg hcap_lt]
        have hrlay : RustLayoutOk (cap.toNat * 48) 8 := ⟨⟨hsz_pos, ⟨3, rfl⟩, by omega⟩, by decide⟩
        wp_call hdealloc (ptr, cap.toNat * 48, 8, M.stepEvents evs_m st)
        apply SepWP.fold (freeOnlyPool_step_dealloc A lim st _ evs_m hevs_m (cap.toNat * 48) 8)
          (by sep_focus)
        refine sepWP_let_state fun sc hsc => ?_
        refine SepWP.weaken_pre
          (weaken_perm
            (word_and_32_rest_entails_40_off p0 $off $off8 cap ho8
              (freeOnlyPool A lim st sc ∗ stackAt fsp extHookStack ∗ Frame))
            (by subst hsc; rw [hsp_m]; sep_ac_rfl)) ?_
        subst hsc
        try wp_done
)

prove_dir_nontail_placed stores_dir_signed_placed stores_loop0_placed (80#64) (88#64) (96#64) (104#64) 0 0 1 3
prove_dir_nontail_placed stores_dir_onetime_placed stores_loop1_placed (200#64) (208#64) (216#64) (224#64) 4 1 3 7
prove_dir_nontail_placed stores_dir_sessions_placed stores_loop2_placed (240#64) (248#64) (256#64) (264#64) 7 2 5 10

def dropDirPairRawSpecPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropDirPairGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl {
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗ dirRawAt A.repAlloc x.a x.d0.changed ∗
        dirRawAt A.repAlloc (x.a + 40#64) x.d1.changed ∗ A.pool lim st s ∗ stackAt s.sp idExactStk
    post := fun (x, st) s0 sf =>
      ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 80 ∗ freeOnlyPool A lim st sf ∗ stackAt s0.sp idExactStk
  }

def dropStoresRawSpecPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropStoresGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl {
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
        dirAt A.repAlloc x.a x.g.identity.own ∗ dirAt A.repAlloc (x.a + 40#64) x.g.identity.peers ∗
        dirRawAt A.repAlloc (x.a + 80#64) x.g.signed.changed ∗
        dirAt A.repAlloc (x.a + 120#64) x.g.kyber.oneTime ∗ dirAt A.repAlloc (x.a + 160#64) x.g.kyber.lastResort ∗
        dirRawAt A.repAlloc (x.a + 200#64) x.g.oneTime.changed ∗
        dirRawAt A.repAlloc (x.a + 240#64) x.g.sessions.changed ∗
        dirRawAt A.repAlloc (x.a + 280#64) x.g.pub.changed ∗
        A.pool lim st s ∗ stackAt s.sp storesExactStk
    post := fun (x, st) s0 sf =>
      ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 320 ∗ freeOnlyPool A lim st sf ∗ stackAt s0.sp storesExactStk
  }

set_option maxHeartbeats 1600000 in
private theorem cliDropIdentityFiles_placed_ok_exact [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_549 H) (blkPl_549).base (dropDirPairRawSpecPlaced M A lim) := by
  unfold dropDirPairRawSpecPlaced withLsCodeRoLoaded
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_549 H) hA
  have hloop0 := fun st => id_loop0_placed hA st
  have hloop1 := fun st => id_loop1_placed hA st
  clear hA
  dsimp only [withLsCodeRoLoaded, lsProg_549, RustCliAllocBudget.live, ↓reduceIte,
    BitVec.ofNat_eq_ofNat] at hdealloc hloop0 hloop1 ⊢
  wp_init x s0
  obtain ⟨⟨a, d0, d1⟩, st⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  subst ‹s0.readReg64 _ = a›
  set p0 := s0.readReg64 (Reg.gpr 0#5)
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_id_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono (dirRawAt_expose A.repAlloc p0 d0.changed)
      (sepConj_mono_right (sepConj_mono_left (freeOnlyPool_intro_nil A lim st s0)))) ?_
  wp_pull_exists
  rename_i cap0 ptr0
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜d0.changed.length ≤ cap0.toNat ∧ cap0.toNat * 48 < 2 ^ 63 ∧
      d0.changed.length * 48 < 2 ^ 63 ∧ ptr0 ≠ 0⌝ ∗
    ((p0 ↦₆₄ cap0) ∗ ((p0 + 8#64) ↦₆₄ ptr0) ∗
      ((p0 + 16#64) ↦₆₄ BitVec.ofNat 64 d0.changed.length) ∗
      arrayAt (dirEntryAt A.repAlloc) 48 ptr0 d0.changed ∗
      (if cap0 = 0 then emp
       else A.repAlloc.live ptr0 (cap0.toNat * 48) 8 ∗
         memRegion (ptr0 + BitVec.ofNat 64 (d0.changed.length * 48))
           ((cap0.toNat - d0.changed.length) * 48)) ∗
      memRegion (p0 + 24#64) 16 ∗ dirRawAt A.repAlloc (p0 + 40#64) d1.changed ∗
      freeOnlyPool A lim st s0 ∗ stackAt (s0.sp - 48#64) extHookStack ∗
      ((s0.sp - 48#64) ↦₆₄ _) ∗ ((s0.sp - 40#64) ↦₆₄ _) ∗
      ((s0.sp - 32#64) ↦₆₄ _) ∗ ((s0.sp - 24#64) ↦₆₄ _) ∗
      ((s0.sp - 16#64) ↦₆₄ _) ∗ ((s0.sp - 8#64) ↦₆₄ _)) by sep_ac_rfl)) ?_
  refine SepWP.pure_elim ?_
  rintro ⟨hlen0_le, hcap0_lt, hlen0_lt, hptr0_ne⟩
  refine seq_cleanX_placed
    (mid := (blkPl_549).base + (words_insn_off% (blkLib_549).text.code "bl" 2 + 4#64))
    (P_mid := fun sm => memRegion p0 40 ∗ dirRawAt A.repAlloc (p0 + 40#64) d1.changed ∗
      freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 48#64) extHookStack ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = p0)
    hcrl0 ?_ ?_
  · refine seq_cleanX_placed
      (mid := (blkPl_549).base + (words_insn_off% (blkLib_549).text.code "b" 1 + 4#64))
      (P_mid := fun sm => (p0 ↦₆₄ cap0) ∗ ((p0 + 8#64) ↦₆₄ ptr0) ∗
        ((p0 + 16#64) ↦₆₄ BitVec.ofNat 64 d0.changed.length) ∗
        memRegion ptr0 (d0.changed.length * 48) ∗
        (if cap0 = 0 then emp
         else A.repAlloc.live ptr0 (cap0.toNat * 48) 8 ∗
           memRegion (ptr0 + BitVec.ofNat 64 (d0.changed.length * 48))
             ((cap0.toNat - d0.changed.length) * 48)) ∗
        memRegion (p0 + 24#64) 16 ∗ dirRawAt A.repAlloc (p0 + 40#64) d1.changed ∗
        freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 48#64) extHookStack ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 (Reg.gpr 19#5) = p0 ∧ sm.readReg64 (Reg.gpr 20#5) = ptr0)
      hcrl0 ?_ ?_
    · cases hc0 : d0.changed with
      | nil =>
        simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
        conv => arg 4; dsimp only [freeOnlyPool]
        wp_pull_exists; rename_i evs_0n
        refine SepWP.focus_pure (by sep_focus) fun hevs_0n => ?_
        wp_steps_sync_pool ((blkPl_549).base + (words_insn_off% (blkLib_549).text.code "b" 1 + 4#64))
        apply SepWP.fold (freeOnlyPool_keep A lim st _ evs_0n hevs_0n) (by sep_focus)
        try wp_done
      | cons hd tl =>
        rw [hc0] at hlen0_lt
        have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) (by omega)
        conv => arg 4; dsimp only [freeOnlyPool]
        wp_pull_exists; rename_i evs_0p
        refine SepWP.focus_pure (by sep_focus) fun hevs_0p => ?_
        apply sepWP_seq_lscro
          (mid := (blkPl_549).base + (words_insn_off% (blkLib_549).text.code "b.cond" 0 + 4#64))
          hcrl0
        wp_steps_sync_pool
          ((blkPl_549).base + (words_insn_off% (blkLib_549).text.code "b.cond" 0 + 4#64))
        apply SepWP.fold (freeOnlyPool_keep A lim st _ evs_0p hevs_0p) (by sep_focus)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_p
        refine sepWP_let_state fun sc hsc => ?_
        have hpre_eq :
            (freeOnlyPool A lim st sc ∗
              (p0 ↦₆₄ cap0) ∗ ((p0 + 8#64) ↦₆₄ ptr0) ∗
              ((p0 + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
              arrayAt (dirEntryAt A.repAlloc) 48 ptr0 (hd :: tl) ∗
              (if cap0 = 0 then emp
               else A.repAlloc.live ptr0 (cap0.toNat * 48) 8 ∗
                 memRegion (ptr0 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                   ((cap0.toNat - (hd :: tl).length) * 48)) ∗
              memRegion (p0 + 24#64) 16 ∗ dirRawAt A.repAlloc (p0 + 40#64) d1.changed ∗
              stackAt (s0.sp - 48#64) extHookStack ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) =
            (arrayAt (dirEntryAt A.repAlloc) 48 ptr0 (hd :: tl) ∗
              freeOnlyPool A lim st sc ∗ stackAt (s0.sp - 48#64) extHookStack ∗
              ((p0 ↦₆₄ cap0) ∗ ((p0 + 8#64) ↦₆₄ ptr0) ∗
                ((p0 + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                (if cap0 = 0 then emp
                 else A.repAlloc.live ptr0 (cap0.toNat * 48) 8 ∗
                   memRegion (ptr0 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                     ((cap0.toNat - (hd :: tl).length) * 48)) ∗
                memRegion (p0 + 24#64) 16 ∗ dirRawAt A.repAlloc (p0 + 40#64) d1.changed ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) := by
          sep_ac_rfl
        subst hsc
        rw [hpre_eq]
        refine SepWP.mono
          (hloop0 st s0 (s0.sp - 48#64) p0 ptr0 hfsp_align (hd :: tl) ptr0 _ _
            (List.cons_ne_nil _ _) hlen0_lt (by wp_norm_goal) (by wp_norm_lhs) hcrl_p
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            rfl rfl rfl rfl) ?_
        intro sm Pm _ _ hh
        exact ⟨Entails.trans hh.1 (Entails.of_eq (by sep_ac_rfl)), hh.2⟩
    · intro sm hpcm hrunm hcrlm
        ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx19_m, hx20_m⟩
      refine SepWP.weaken_pre
        (post_dir_loop_weaken A.repAlloc p0 cap0 ptr0 d0.changed.length hlen0_le hcap0_lt _) ?_
      conv => arg 4; dsimp only [freeOnlyPool]
      wp_pull_exists; rename_i evs_0m
      refine SepWP.focus_pure (by sep_focus) fun hevs_0m => ?_
      by_cases hcap0 : (cap0 == 0#64) = true <;>
        simp only [hcap0, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
      · wp_steps_sync_pool
          ((blkPl_549).base + (words_insn_off% (blkLib_549).text.code "bl" 2 + 4#64))
        apply SepWP.fold (freeOnlyPool_keep A lim st _ evs_0m hevs_0m) (by sep_focus)
        refine sepWP_let_state fun sc hsc => ?_
        refine SepWP.weaken_pre
          (weaken_perm
            (word_and_32_rest_entails_40 p0 cap0
              (dirRawAt A.repAlloc (p0 + 40#64) d1.changed ∗ freeOnlyPool A lim st sc ∗
                stackAt (s0.sp - 48#64) extHookStack ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
            (by subst hsc; sep_ac_rfl)) ?_
        subst hsc
        try wp_done
      · have hcap_pos := pos_of_beq_zero_false hcap0
        have hsz_pos : 0 < cap0.toNat * 48 := Nat.mul_pos hcap_pos (by decide)
        apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrlm
        wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_cm
        have ⟨hcl_cm, hro_cm⟩ := hcrl_cm
        rw [mul_48_reg hcap0_lt]
        have hrlay : RustLayoutOk (cap0.toNat * 48) 8 := ⟨⟨hsz_pos, ⟨3, rfl⟩, by omega⟩, by decide⟩
        wp_call hdealloc (ptr0, cap0.toNat * 48, 8, M.stepEvents evs_0m st)
        apply SepWP.fold (freeOnlyPool_step_dealloc A lim st _ evs_0m hevs_0m (cap0.toNat * 48) 8)
          (by sep_focus)
        refine sepWP_let_state fun sc hsc => ?_
        refine SepWP.weaken_pre
          (weaken_perm
            (word_and_32_rest_entails_40 p0 cap0
              (dirRawAt A.repAlloc (p0 + 40#64) d1.changed ∗ freeOnlyPool A lim st sc ∗
                stackAt (s0.sp - 48#64) extHookStack ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
            (by subst hsc; try rw [hsp_m]; sep_ac_rfl)) ?_
        subst hsc
        try wp_done
  ·
    intro s1 hpc1 hrun1 hcrl1
      ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    have ho1_8 : (p0 + 40#64) + 8#64 = p0 + 48#64 := by bv_omega
    have ho1_16 : (p0 + 40#64) + 16#64 = p0 + 56#64 := by bv_omega
    have ho1_24 : (p0 + 40#64) + 24#64 = p0 + 64#64 := by bv_omega
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_left
        (dirRawAt_expose_off A.repAlloc p0 40#64 48#64 56#64 64#64
          ho1_8 ho1_16 ho1_24 d1.changed))) ?_
    wp_pull_exists
    rename_i cap1 ptr1
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜d1.changed.length ≤ cap1.toNat ∧ cap1.toNat * 48 < 2 ^ 63 ∧
        d1.changed.length * 48 < 2 ^ 63 ∧ ptr1 ≠ 0⌝ ∗
      (((p0 + 40#64) ↦₆₄ cap1) ∗ ((p0 + 48#64) ↦₆₄ ptr1) ∗
        ((p0 + 56#64) ↦₆₄ BitVec.ofNat 64 d1.changed.length) ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr1 d1.changed ∗
        (if cap1 = 0 then emp
         else A.repAlloc.live ptr1 (cap1.toNat * 48) 8 ∗
           memRegion (ptr1 + BitVec.ofNat 64 (d1.changed.length * 48))
             ((cap1.toNat - d1.changed.length) * 48)) ∗
        memRegion (p0 + 64#64) 16 ∗ memRegion p0 40 ∗
        freeOnlyPool A lim st s1 ∗ stackAt (s0.sp - 48#64) extHookStack ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by sep_ac_rfl)) ?_
    refine SepWP.pure_elim ?_
    rintro ⟨hlen1_le, hcap1_lt, hlen1_lt, hptr1_ne⟩
    refine seq_cleanX_placed
      (mid := (blkPl_549).base + (words_insn_off% (blkLib_549).text.code "b" 3 + 4#64))
      (P_mid := fun sm => ((p0 + 40#64) ↦₆₄ cap1) ∗ ((p0 + 48#64) ↦₆₄ ptr1) ∗
        ((p0 + 56#64) ↦₆₄ BitVec.ofNat 64 d1.changed.length) ∗
        memRegion ptr1 (d1.changed.length * 48) ∗
        (if cap1 = 0 then emp
         else A.repAlloc.live ptr1 (cap1.toNat * 48) 8 ∗
           memRegion (ptr1 + BitVec.ofNat 64 (d1.changed.length * 48))
             ((cap1.toNat - d1.changed.length) * 48)) ∗
        memRegion (p0 + 64#64) 16 ∗ memRegion p0 40 ∗
        freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 48#64) extHookStack ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 (Reg.gpr 19#5) = p0 ∧ sm.readReg64 (Reg.gpr 20#5) = ptr1)
      hcrl1 ?_ ?_
    · cases hc1 : d1.changed with
      | nil =>
        simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
        conv => arg 4; dsimp only [freeOnlyPool]
        wp_pull_exists; rename_i evs_1n
        refine SepWP.focus_pure (by sep_focus) fun hevs_1n => ?_
        wp_steps_sync_pool ((blkPl_549).base + (words_insn_off% (blkLib_549).text.code "b" 3 + 4#64))
        apply SepWP.fold (freeOnlyPool_keep A lim st _ evs_1n hevs_1n) (by sep_focus)
        try wp_done
      | cons hd tl =>
        rw [hc1] at hlen1_lt
        have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) (by omega)
        conv => arg 4; dsimp only [freeOnlyPool]
        wp_pull_exists; rename_i evs_1p
        refine SepWP.focus_pure (by sep_focus) fun hevs_1p => ?_
        apply sepWP_seq_lscro
          (mid := (blkPl_549).base + (words_insn_off% (blkLib_549).text.code "b.cond" 1 + 4#64))
          hcrl1
        wp_steps_sync_pool
          ((blkPl_549).base + (words_insn_off% (blkLib_549).text.code "b.cond" 1 + 4#64))
        apply SepWP.fold (freeOnlyPool_keep A lim st _ evs_1p hevs_1p) (by sep_focus)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_p
        refine sepWP_let_state fun sc hsc => ?_
        have hpre_eq :
            (freeOnlyPool A lim st sc ∗
              ((p0 + 40#64) ↦₆₄ cap1) ∗ ((p0 + 48#64) ↦₆₄ ptr1) ∗
              ((p0 + 56#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
              arrayAt (dirEntryAt A.repAlloc) 48 ptr1 (hd :: tl) ∗
              (if cap1 = 0 then emp
               else A.repAlloc.live ptr1 (cap1.toNat * 48) 8 ∗
                 memRegion (ptr1 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                   ((cap1.toNat - (hd :: tl).length) * 48)) ∗
              memRegion (p0 + 64#64) 16 ∗ memRegion p0 40 ∗
              stackAt (s0.sp - 48#64) extHookStack ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) =
            (arrayAt (dirEntryAt A.repAlloc) 48 ptr1 (hd :: tl) ∗
              freeOnlyPool A lim st sc ∗ stackAt (s0.sp - 48#64) extHookStack ∗
              (((p0 + 40#64) ↦₆₄ cap1) ∗ ((p0 + 48#64) ↦₆₄ ptr1) ∗
                ((p0 + 56#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                (if cap1 = 0 then emp
                 else A.repAlloc.live ptr1 (cap1.toNat * 48) 8 ∗
                   memRegion (ptr1 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                     ((cap1.toNat - (hd :: tl).length) * 48)) ∗
                memRegion (p0 + 64#64) 16 ∗ memRegion p0 40 ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) := by
          sep_ac_rfl
        subst hsc
        rw [hpre_eq]
        refine SepWP.mono
          (hloop1 st s0 (s0.sp - 48#64) p0 ptr1 hfsp_align (hd :: tl) ptr1 _ _
            (List.cons_ne_nil _ _) hlen1_lt (by wp_norm_goal) (by wp_norm_lhs) hcrl_p
            ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
            hx19_1 rfl rfl rfl) ?_
        intro sm Pm _ _ hh
        exact ⟨Entails.trans hh.1 (Entails.of_eq (by sep_ac_rfl)), hh.2⟩
    · intro sm hpcm hrunm hcrlm
        ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx19_m, hx20_m⟩
      refine SepWP.weaken_pre
        (post_dir_loop_weaken_off A.repAlloc p0 40#64 48#64 56#64 64#64 cap1 ptr1
          ho1_8 ho1_16 ho1_24 d1.changed.length hlen1_le hcap1_lt _) ?_
      conv => arg 4; dsimp only [freeOnlyPool]
      wp_pull_exists; rename_i evs_1m
      refine SepWP.focus_pure (by sep_focus) fun hevs_1m => ?_
      by_cases hcap1 : (cap1 == 0#64) = true <;>
        simp only [hcap1, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
      · wp_steps_sync_pool (s0.readReg64 .lr)
        apply SepWP.fold (freeOnlyPool_keep A lim st _ evs_1m hevs_1m) (by sep_focus)
        refine sepWP_let_state fun sc hsc => ?_
        refine SepWP.weaken_pre
          (weaken_perm
            (id_cap0_ret_weaken p0 cap1 (freeOnlyPool A lim st sc) s0.sp
              (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
              (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
              (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
            (by subst hsc; sep_ac_rfl)) ?_
        subst hsc
        try wp_done
      · have hcap_pos := pos_of_beq_zero_false hcap1
        have hsz_pos : 0 < cap1.toNat * 48 := Nat.mul_pos hcap_pos (by decide)
        apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrlm
        wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
        refine sepWP_let_state fun sc hsc => ?_
        refine SepWP.weaken_pre
          (weaken_perm
            (id_tail_dealloc_pre_weaken p0 cap1
              (A.repAlloc.live ptr1 (cap1.toNat * 48) 8 ∗ memRegion ptr1 (cap1.toNat * 48))
              (A.pool lim (M.stepEvents evs_1m st) sc) s0.sp
              (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
              (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
              (s0.readReg64 (Reg.gpr 20#5))
              (s0.readReg64 (Reg.gpr 19#5)))
            (by subst hsc; sep_ac_rfl)) ?_
        subst hsc
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_ct
        have ⟨hcl_ct, hro_ct⟩ := hcrl_ct
        rw [mul_48_reg hcap1_lt]
        have hrlay : RustLayoutOk (cap1.toNat * 48) 8 := ⟨⟨hsz_pos, ⟨3, rfl⟩, by omega⟩, by decide⟩
        wp_call hdealloc (ptr1, cap1.toNat * 48, 8, M.stepEvents evs_1m st)
        apply SepWP.fold (freeOnlyPool_step_dealloc A lim st _ evs_1m hevs_1m (cap1.toNat * 48) 8)
          (by sep_focus)
        refine sepWP_let_state fun sc2 hsc2 => ?_
        refine SepWP.weaken_pre
          (weaken_perm (id_tail_dealloc_post p0 (freeOnlyPool A lim st sc2) s0.sp)
            (by subst hsc2; sep_ac_rfl)) ?_
        subst hsc2
        try wp_done

end DropStoresPlacedBudgetHelpers

/-- Proves the budget-threaded `dropDirPairSpecPlaced` contract on block `549` at stack budgets `48 + extHookStack ≤ stk ≤ 2 ^ 64`. -/
theorem cliDropIdentityFiles_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (stk : Nat) (hstk : 48 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_549 H) (blkPl_549).base (dropDirPairSpecPlaced M A lim stk) := by
  have hexact := cliDropIdentityFiles_placed_ok_exact hA
  refine subroutine_ok_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  let F : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - idExactStk)
  have hsplit : stackAt s0.sp stk = stackAt s0.sp idExactStk ∗ F :=
    stackAt_sub_split hstk hstk64 s0.sp
  have hpre1 : s0.mem ⊨
      (dropDirPairRawSpecPlaced M A lim).pre (x, st) s0 ∗
        ((roPathAt x.d0.path ∗ roPathAt x.d1.path) ∗ (F ∗ R)) := by
    simp only [dropDirPairSpecPlaced, dropDirPairRawSpecPlaced,
      withLsCodeRoLoaded, dropDirPairSpec] at hpre ⊢
    rw [hsplit] at hpre
    refine Satisfies.mono ?_ hpre
    refine Entails.trans (Entails.of_eq (show _ =
        (dirAt A.repAlloc x.a x.d0 ∗ dirAt A.repAlloc (x.a + 0x28#64) x.d1) ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
            ⌜s0.readReg64 .x0 = x.a ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
            A.pool lim st s0 ∗ stackAt s0.sp idExactStk ∗ F ∗ R) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (id_entry_raw_ro A.repAlloc x.a x.d0 x.d1)) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  have hpre2 : s0.mem ⊨ (dropDirPairRawSpecPlaced M A lim).pre (x, st) s0 ∗ (F ∗ R) :=
    Satisfies.drop_mid hpre1
  refine reaches_pc_mono
    (subroutine_ok_apply_full hexact (x, st) (F ∗ R) hpc hrun hpre2 hsp) ?_
  intro sf _ _ ⟨hpost, hcc⟩
  refine ⟨?_, hcc⟩
  simp only [dropDirPairSpecPlaced, dropDirPairRawSpecPlaced,
    withLsCodeRoLoaded, dropDirPairSpec, freeOnlyPool] at hpost ⊢
  rw [hsplit]
  refine Satisfies.mono ?_ hpost
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro evs
  have hord :
      (⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 80 ∗
        (⌜∀ ev ∈ evs, ∃ al sz, ev = .free al sz⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        stackAt s0.sp idExactStk) ∗ F ∗ R =
      ⌜sf.trace = s0.trace⌝ ∗ (⌜∀ ev ∈ evs, ∃ al sz, ev = .free al sz⌝ ∗
        ((memRegion x.a 80 ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp idExactStk ∗ F) ∗ R)) := by
    sep_ac_rfl
  rw [hord]
  apply Entails.pure_left; intro htr
  apply Entails.pure_left; intro hevs
  refine Entails.sepExists_right evs (sepConj_mono_left ?_)
  rw [pure_sepConj_of_true ⟨htr, hevs⟩]
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresPlacedBudgetAux
