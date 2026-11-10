/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Plain and String-Carrying `SignalProtocolError` Drop Helpers

Proves exact-stack `[LibsignalPlacement]` budget-threaded drop contracts for plain and
`withString` variants of `SignalProtocolError`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (SignalProtocolError)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement LibsignalRoLoaded lsmpl lsroCheck
  lsro_intro_chk lsρ
)
open CryptoVerification.RustHeap (LayoutOk RustAlloc vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropSpeStackX speJumpTable)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded
)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553 lsProg_553)
open CryptoVerification.SignalSession.Cli.RunDrop (
  PlainSpeTag StrSpeTag plainSpeTags speOwnedAt strSpeTags
)
open CryptoVerification.SignalSession.Cli.RunProofs.DropSpeOwnedHelpers (
  SatEntails SpecAt cells4_entails_stack_bottomX spe_kem_pre_weaken_fullX spe_noop_pre_weaken_fullX
  spe_plain_tbl_pre_weakenX spe_str_words_entails_48 spe_tail_dealloc_postX
  stackAt_dropSpeX_split stack_restore_32_speX subroutine_ok_of_pure_pre
  subroutine_ok_pointwise vecU8_at_8_exposeX weaken_pre_sat
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk
  rustDeallocEvents
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (dealloc_lscro_of_cli)

section DropSpeOwnedPlacedBudgetHelpers

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

def freeOnlyPool {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent,
    ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s

theorem freeOnlyPool_nil {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ freeOnlyPool A lim st s := by
  unfold freeOnlyPool
  refine Entails.sepExists_right [] ?_
  rw [M.stepEvents_nil]
  exact Entails.pure_right FreeOnlyEvs.nil (Entails.refl _)

theorem freeOnlyPool_dealloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (sz al : Nat) :
    A.pool lim (M.stepEvents (rustDeallocEvents sz al) st) s ⊢
      freeOnlyPool A lim st s := by
  unfold freeOnlyPool
  exact Entails.sepExists_right (rustDeallocEvents sz al)
    (Entails.pure_right (FreeOnlyEvs.singleton al sz) (Entails.refl _))

abbrev cliSpeJumpTableSym : String :=
  "libsignal_cli:.rodata.core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError>"

theorem lsroCheck_cliSpeJumpTable :
    lsroCheck cliSpeJumpTableSym speJumpTable = true := by
  rfl_kernel

theorem intro_rodata_cliSpeJumpTable_placed [LibsignalPlacement]
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWP prog target_pc s
      (((lsρ cliSpeJumpTableSym) ↦ᵣ speJumpTable) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  have hR := h R
  rw [sepConj_assoc] at hR
  exact hR (lsro_intro_chk hro lsroCheck_cliSpeJumpTable hm)

theorem cliSpeJumpTable_byte_placed (tbl : BitVec 64) (i : Nat) (b : BitVec 8)
    (heq : speJumpTable = speJumpTable.take i ++ (b :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i) :
    SatEntails (tbl ↦ᵣ speJumpTable) ((tbl + BitVec.ofNat 64 i) ↦₈ᵣ b) := by
  have h :
      (tbl ↦ᵣ speJumpTable) =
      (tbl ↦ᵣ speJumpTable.take i) ∗
        (((tbl + BitVec.ofNat 64 i) ↦₈ᵣ b) ∗
         ((tbl + BitVec.ofNat 64 i + 1#64) ↦ᵣ speJumpTable.drop (i + 1))) := by
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen]
  rw [h]
  exact SatEntails.trans (SatEntails.drop_left _ _) (SatEntails.drop_right _ _)

private theorem plain_tbl_weaken_placed (tbl a : BitVec 64) (i : Nat) (w : BitVec 64)
    (hw : speWord i = w)
    (heq : speJumpTable = speJumpTable.take i ++ (0x1b#8 :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i)
    (rest : SepProp) :
    SatEntails
      ((tbl ↦ᵣ speJumpTable) ∗ ((a ↦₆₄ speWord i) ∗ memRegion (a + 8#64) 40 ∗ rest))
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ((tbl + BitVec.ofNat 64 i) ↦₈ᵣ 0x1b#8) ∗ rest) :=
  spe_plain_tbl_pre_weakenX a i w hw (cliSpeJumpTable_byte_placed tbl i 0x1b#8 heq hlen) rest

def dropSpePlainRawSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × Nat) × M.σ) where
  pre := fun (⟨a, i⟩, st) s =>
    (⌜s.readReg64 .x0 = a⌝ ∗
      ((a ↦₆₄ speWord i) ∗ memRegion (a + 8#64) 40) ∗
      A.pool lim st s ∗ stackAt s.sp dropSpeStackX) ∗
      ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝
  post := fun (⟨a, _⟩, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion a 48 ∗ A.pool lim st sf ∗ stackAt s0.sp dropSpeStackX

private theorem spe_noop_pre_weaken_pool_first (a w sp fp lr x20 x19 : BitVec 64)
    (ro pool : SepProp) :
    SatEntails
      (pool ∗ (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro ∗
        stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) :=
  SatEntails.trans (SatEntails.of_eq (by sep_ac_rfl))
    (spe_noop_pre_weaken_fullX a w sp fp lr x20 x19 ro pool)

private theorem spe_kem_pre_weaken_pool_first (a w sp fp lr x20 x19 : BitVec 64)
    (pool : SepProp) :
    pool ∗ (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗
      stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX :=
  Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (spe_kem_pre_weaken_fullX a w sp fp lr x20 x19 pool)

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_plainTag_tbl1_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {i : Nat} (hi : i ∈ [2, 3, 4, 5, 6, 7, 8, 9, 10]) (a : BitVec 64) (st : M.σ) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpePlainRawSpec A lim) (⟨a, i⟩, st)) := by
  refine subroutine_ok_of_pure_pre hi ?_
  simp only [SpecAt, dropSpePlainRawSpec, pure_sepConj_pure_assoc]
  dsimp only [lsProg_553, ↓reduceIte]
  wp_init u s0
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  have hmem : i ∈ [2, 3, 4, 5, 6, 7, 8, 9, 10] := ‹_›
  subst ‹s0.readReg64 _ = a›
  refine intro_rodata_cliSpeJumpTable_placed hcrl0.2 ?_
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 2 0x8000000000000002#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 3 0x8000000000000003#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 4 0x8000000000000004#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 5 0x8000000000000005#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 6 0x8000000000000006#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 7 0x8000000000000007#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 8 0x8000000000000008#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 9 0x8000000000000009#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 10 0x800000000000000a#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_plainTag_tbl2_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {i : Nat} (hi : i ∈ [11, 13, 14, 15, 16, 17, 20, 21, 23]) (a : BitVec 64) (st : M.σ) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpePlainRawSpec A lim) (⟨a, i⟩, st)) := by
  refine subroutine_ok_of_pure_pre hi ?_
  simp only [SpecAt, dropSpePlainRawSpec, pure_sepConj_pure_assoc]
  dsimp only [lsProg_553, ↓reduceIte]
  wp_init u s0
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  have hmem : i ∈ [11, 13, 14, 15, 16, 17, 20, 21, 23] := ‹_›
  subst ‹s0.readReg64 _ = a›
  refine intro_rodata_cliSpeJumpTable_placed hcrl0.2 ?_
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 11 0x800000000000000b#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 13 0x800000000000000d#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 14 0x800000000000000e#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 15 0x800000000000000f#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 16 0x8000000000000010#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 17 0x8000000000000011#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 20 0x8000000000000014#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 21 0x8000000000000015#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken_placed (lsρ cliSpeJumpTableSym) _ 23 0x8000000000000017#64 rfl rfl rfl _) ?_
    wp_steps_sync_pool (s0.readReg64 .lr); refine weaken_pre_sat (spe_noop_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _ _) ?_; wp_done

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_plainTag_hi_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {i : Nat} (hi : i ∈ [28, 29, 30, 31, 32, 33, 34]) (a : BitVec 64) (st : M.σ) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpePlainRawSpec A lim) (⟨a, i⟩, st)) := by
  refine subroutine_ok_of_pure_pre hi ?_
  simp only [SpecAt, dropSpePlainRawSpec, pure_sepConj_pure_assoc]
  dsimp only [lsProg_553, ↓reduceIte]
  wp_init u s0
  have hmem : i ∈ [28, 29, 30, 31, 32, 33, 34] := ‹_›
  subst ‹s0.readReg64 _ = a›
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [show speWord 28 = 0x800000000000001c#64 from rfl]
    wp_steps_sync_pool (s0.readReg64 .lr); refine SepWP.weaken_pre (spe_kem_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 29 = 0x800000000000001d#64 from rfl]
    wp_steps_sync_pool (s0.readReg64 .lr); refine SepWP.weaken_pre (spe_kem_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 30 = 0x800000000000001e#64 from rfl]
    wp_steps_sync_pool (s0.readReg64 .lr); refine SepWP.weaken_pre (spe_kem_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 31 = 0x800000000000001f#64 from rfl]
    wp_steps_sync_pool (s0.readReg64 .lr); refine SepWP.weaken_pre (spe_kem_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 32 = 0x8000000000000020#64 from rfl]
    wp_steps_sync_pool (s0.readReg64 .lr); refine SepWP.weaken_pre (spe_kem_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 33 = 0x8000000000000021#64 from rfl]
    wp_steps_sync_pool (s0.readReg64 .lr); refine SepWP.weaken_pre (spe_kem_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 34 = 0x8000000000000022#64 from rfl]
    wp_steps_sync_pool (s0.readReg64 .lr); refine SepWP.weaken_pre (spe_kem_pre_weaken_pool_first _ _ s0.sp _ _ _ _ _) ?_; wp_done

theorem cliDropSpeOwned_plain_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {i : Nat} (hi : PlainSpeTag i) (a : BitVec 64) (st : M.σ) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpePlainRawSpec A lim) (⟨a, i⟩, st)) := by
  have hsplit :
      i ∈ [2, 3, 4, 5, 6, 7, 8, 9, 10] ∨
      i ∈ [11, 13, 14, 15, 16, 17, 20, 21, 23] ∨
      i ∈ [28, 29, 30, 31, 32, 33, 34] := by
    simp only [PlainSpeTag, plainSpeTags, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega
  rcases hsplit with h1 | h2 | h3
  · exact cliDropSpeOwned_plainTag_tbl1_placed_ok_x h1 a st
  · exact cliDropSpeOwned_plainTag_tbl2_placed_ok_x h2 a st
  · exact cliDropSpeOwned_plainTag_hi_placed_ok_x h3 a st

/-! ## String-carrying (`withString`) error drop helpers -/
def dropSpeWithStrRawSpecXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × Nat) × M.σ) where
  pre := fun (⟨a, i⟩, st) s =>
    (⌜s.readReg64 .x0 = a ∧
        LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      ((a ↦₆₄ speWord i) ∗ (∃∗ bs : List (BitVec 8), vecU8 A.repAlloc (a + 8#64) bs) ∗
        memRegion (a + 32#64) 16) ∗
      A.pool lim st s ∗ stackAt s.sp dropSpeStackX) ∗
      ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝
  post := fun (⟨a, _⟩, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion a 48 ∗ freeOnlyPool A lim st sf ∗ stackAt s0.sp dropSpeStackX

private theorem spe_str_cap0_pre_weaken_fullX_placed (a w cap ptr sp fp lr x20 x19 : BitVec 64)
    (ro pool : SepProp) :
    SatEntails
      (pool ∗ (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (spe_str_words_entails_48 a w cap ptr)
  have hst := SatEntails.of_entails (stack_restore_32_speX sp fp lr x20 x19)
  have hreord :
      pool ∗ (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24) ∗
        ((ro ∗ pool) ∗
          (stackAt (sp - 32#64) extHookStack ∗
            ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
            ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by sep_ac_rfl
  rw [hreord]
  exact SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro hst)

private theorem spe_tail_dealloc_pre_weakenX_placed (a w cap ptr sp : BitVec 64)
    (fp lr x20 x19 : BitVec 64) (ro live1 live2 pool : SepProp) :
    SatEntails
      (pool ∗ (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ live1 ∗ live2 ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack ∗
        (live1 ∗ live2)) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (spe_str_words_entails_48 a w cap ptr)
  have hst := SatEntails.of_entails (cells4_entails_stack_bottomX sp fp lr x20 x19)
  have hreord :
      pool ∗ (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ live1 ∗ live2 ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) =
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24) ∗
        ((ro ∗ pool) ∗
         ((stackAt (sp - 32#64) extHookStack ∗
           ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
           ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ∗ (live1 ∗ live2))) := by sep_ac_rfl
  rw [hreord]
  refine SatEntails.trans
    (SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro (SatEntails.sepConj_mono_left hst))) ?_
  exact SatEntails.of_eq (by sep_ac_rfl)

private theorem str_tbl_weaken_placed (A : RustAlloc) (tbl a : BitVec 64) (i : Nat)
    (w : BitVec 64) (bs : List (BitVec 8))
    (hw : speWord i = w)
    (heq : speJumpTable = speJumpTable.take i ++ (0x00#8 :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i)
    (rest : SepProp) :
    SatEntails
      ((tbl ↦ᵣ speJumpTable) ∗
        ((a ↦₆₄ speWord i) ∗ vecU8 A (a + 8#64) bs ∗ memRegion (a + 32#64) 16 ∗ rest))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ w) ∗
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ((tbl + BitVec.ofNat 64 i) ↦₈ᵣ 0x00#8) ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ rest) := by
  subst hw
  have hbyte := cliSpeJumpTable_byte_placed tbl i 0x00#8 heq hlen
  have grouped :
      (a ↦₆₄ speWord i) ∗ vecU8 A (a + 8#64) bs ∗ memRegion (a + 32#64) 16 ∗ rest =
      (a ↦₆₄ speWord i) ∗ (vecU8 A (a + 8#64) bs ∗ memRegion (a + 32#64) 16) ∗ rest := by
    sep_ac_rfl
  rw [grouped]
  refine SatEntails.trans
    (SatEntails.sepConj_mono hbyte
      (SatEntails.sepConj_mono_right
        (SatEntails.sepConj_mono_left (SatEntails.of_entails (vecU8_at_8_exposeX A a bs))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails.sepExists_elim; intro cap
  apply SatEntails.sepExists_elim; intro ptr
  refine SatEntails.sepExists_right cap (SatEntails.sepExists_right ptr ?_)
  exact SatEntails.of_eq (by sep_ac_rfl)

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_withStr1_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    {i : Nat} (h4 : i ∈ [0, 1, 12, 18]) (a : BitVec 64) (st : M.σ) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpeWithStrRawSpecXPlaced A lim) (⟨a, i⟩, st)) := by
  refine subroutine_ok_of_pure_pre h4 ?_
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_553 H) hA
  clear hA
  simp only [SpecAt, dropSpeWithStrRawSpecXPlaced, pure_sepConj_pure_assoc]
  dsimp only [withLsCodeRoLoaded, lsProg_553, RustCliAllocBudget.live, ↓reduceIte] at hdealloc ⊢
  wp_init u s0
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  have hmem : i ∈ [0, 1, 12, 18] := ‹_›
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  subst ‹s0.readReg64 _ = a›
  refine intro_rodata_cliSpeJumpTable_placed hcrl0.2 ?_
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · refine weaken_pre_sat (str_tbl_weaken_placed A.repAlloc (lsρ cliSpeJumpTableSym) _ 0 0x8000000000000000#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps_sync_pool (s0.readReg64 .lr)
      refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus); wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) fun hlay => ?_
      have hrlay : RustLayoutOk cap.toNat 1 := ⟨hlay, hal1⟩
      have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      rcases hlay with ⟨hpos_cap, _, hlt_cap⟩
      apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1, st)
      apply SepWP.fold (freeOnlyPool_dealloc A lim st _ cap.toNat 1) (by sep_focus)
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (spe_tail_dealloc_postX _ _ s0.sp)) ?_
      wp_done
  · refine weaken_pre_sat (str_tbl_weaken_placed A.repAlloc (lsρ cliSpeJumpTableSym) _ 1 0x8000000000000001#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps_sync_pool (s0.readReg64 .lr)
      refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus); wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) fun hlay => ?_
      have hrlay : RustLayoutOk cap.toNat 1 := ⟨hlay, hal1⟩
      have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      rcases hlay with ⟨hpos_cap, _, hlt_cap⟩
      apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1, st)
      apply SepWP.fold (freeOnlyPool_dealloc A lim st _ cap.toNat 1) (by sep_focus)
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (spe_tail_dealloc_postX _ _ s0.sp)) ?_
      wp_done
  · refine weaken_pre_sat (str_tbl_weaken_placed A.repAlloc (lsρ cliSpeJumpTableSym) _ 12 0x800000000000000c#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps_sync_pool (s0.readReg64 .lr)
      refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus); wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) fun hlay => ?_
      have hrlay : RustLayoutOk cap.toNat 1 := ⟨hlay, hal1⟩
      have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      rcases hlay with ⟨hpos_cap, _, hlt_cap⟩
      apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1, st)
      apply SepWP.fold (freeOnlyPool_dealloc A lim st _ cap.toNat 1) (by sep_focus)
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (spe_tail_dealloc_postX _ _ s0.sp)) ?_
      wp_done
  · refine weaken_pre_sat (str_tbl_weaken_placed A.repAlloc (lsρ cliSpeJumpTableSym) _ 18 0x8000000000000012#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps_sync_pool (s0.readReg64 .lr)
      refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus); wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) fun hlay => ?_
      have hrlay : RustLayoutOk cap.toNat 1 := ⟨hlay, hal1⟩
      have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      rcases hlay with ⟨hpos_cap, _, hlt_cap⟩
      apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1, st)
      apply SepWP.fold (freeOnlyPool_dealloc A lim st _ cap.toNat 1) (by sep_focus)
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (spe_tail_dealloc_postX _ _ s0.sp)) ?_
      wp_done

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_withStr2_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    {i : Nat} (h4 : i ∈ [22, 24, 25, 27]) (a : BitVec 64) (st : M.σ) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpeWithStrRawSpecXPlaced A lim) (⟨a, i⟩, st)) := by
  refine subroutine_ok_of_pure_pre h4 ?_
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_553 H) hA
  clear hA
  simp only [SpecAt, dropSpeWithStrRawSpecXPlaced, pure_sepConj_pure_assoc]
  dsimp only [withLsCodeRoLoaded, lsProg_553, RustCliAllocBudget.live, ↓reduceIte] at hdealloc ⊢
  wp_init u s0
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  have hmem : i ∈ [22, 24, 25, 27] := ‹_›
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  subst ‹s0.readReg64 _ = a›
  refine intro_rodata_cliSpeJumpTable_placed hcrl0.2 ?_
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · refine weaken_pre_sat (str_tbl_weaken_placed A.repAlloc (lsρ cliSpeJumpTableSym) _ 22 0x8000000000000016#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps_sync_pool (s0.readReg64 .lr)
      refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus); wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) fun hlay => ?_
      have hrlay : RustLayoutOk cap.toNat 1 := ⟨hlay, hal1⟩
      have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      rcases hlay with ⟨hpos_cap, _, hlt_cap⟩
      apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1, st)
      apply SepWP.fold (freeOnlyPool_dealloc A lim st _ cap.toNat 1) (by sep_focus)
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (spe_tail_dealloc_postX _ _ s0.sp)) ?_
      wp_done
  · refine weaken_pre_sat (str_tbl_weaken_placed A.repAlloc (lsρ cliSpeJumpTableSym) _ 24 0x8000000000000018#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps_sync_pool (s0.readReg64 .lr)
      refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus); wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) fun hlay => ?_
      have hrlay : RustLayoutOk cap.toNat 1 := ⟨hlay, hal1⟩
      have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      rcases hlay with ⟨hpos_cap, _, hlt_cap⟩
      apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1, st)
      apply SepWP.fold (freeOnlyPool_dealloc A lim st _ cap.toNat 1) (by sep_focus)
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (spe_tail_dealloc_postX _ _ s0.sp)) ?_
      wp_done
  · refine weaken_pre_sat (str_tbl_weaken_placed A.repAlloc (lsρ cliSpeJumpTableSym) _ 25 0x8000000000000019#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps_sync_pool (s0.readReg64 .lr)
      refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus); wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) fun hlay => ?_
      have hrlay : RustLayoutOk cap.toNat 1 := ⟨hlay, hal1⟩
      have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      rcases hlay with ⟨hpos_cap, _, hlt_cap⟩
      apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1, st)
      apply SepWP.fold (freeOnlyPool_dealloc A lim st _ cap.toNat 1) (by sep_focus)
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (spe_tail_dealloc_postX _ _ s0.sp)) ?_
      wp_done
  · refine weaken_pre_sat (str_tbl_weaken_placed A.repAlloc (lsρ cliSpeJumpTableSym) _ 27 0x800000000000001b#64 _ rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps_sync_pool (s0.readReg64 .lr)
      refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX_placed _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus); wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) fun hlay => ?_
      have hrlay : RustLayoutOk cap.toNat 1 := ⟨hlay, hal1⟩
      have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      rcases hlay with ⟨hpos_cap, _, hlt_cap⟩
      apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX_placed _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩; wp_call hdealloc (ptr, cap.toNat, 1, st)
      apply SepWP.fold (freeOnlyPool_dealloc A lim st _ cap.toNat 1) (by sep_focus)
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (spe_tail_dealloc_postX _ _ s0.sp)) ?_
      wp_done

def dropSpeWithStrSpecXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × { i : Nat // StrSpeTag i }) × M.σ) where
  pre := fun (⟨a, ⟨i, hi⟩⟩, st) s =>
    (⌜s.readReg64 .x0 = a ∧
        LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      speOwnedAt A.repAlloc a (.withString i hi) ∗
      A.pool lim st s ∗ stackAt s.sp dropSpeStackX) ∗
      ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝
  post := fun (⟨a, _⟩, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion a 48 ∗ freeOnlyPool A lim st sf ∗ stackAt s0.sp dropSpeStackX

theorem cliDropSpeOwned_withStr_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_553 H) (blkPl_553).base (dropSpeWithStrSpecXPlaced A lim) := by
  refine subroutine_ok_pointwise fun ⟨⟨a, ⟨i, hi⟩⟩, st⟩ => ?_
  have hraw : subroutine_ok (lsProg_553 H) (blkPl_553).base
      (SpecAt (dropSpeWithStrRawSpecXPlaced A lim) (⟨a, i⟩, st)) := by
    have hsplit : i ∈ [0, 1, 12, 18] ∨ i ∈ [22, 24, 25, 27] := by
      simp only [StrSpeTag, strSpeTags, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    rcases hsplit with h1 | h2
    · exact cliDropSpeOwned_withStr1_placed_ok_x hA h1 a st
    · exact cliDropSpeOwned_withStr2_placed_ok_x hA h2 a st
  exact subroutine_ok_mono hraw
    (fun _ _ _ hp => by
      dsimp only [SpecAt, dropSpeWithStrSpecXPlaced, dropSpeWithStrRawSpecXPlaced,
        speOwnedAt] at hp ⊢
      exact hp)
    (fun _ _ _ _ hp => by
      dsimp only [SpecAt, dropSpeWithStrSpecXPlaced, dropSpeWithStrRawSpecXPlaced] at hp ⊢
      exact hp)

end DropSpeOwnedPlacedBudgetHelpers

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudgetAux
