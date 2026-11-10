/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common

/-!
# Budget-Threaded Relocatable `drop_glue::<SignalProtocolError> [local#3]` (Block `552`)

Verifies `dropSpeSpecX` on Block `552` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (InvalidMessageReason MessageType SignalProtocolError)
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement LibsignalRoLoaded
  lsmpl lsro_intro_chk lsρ
)
open CryptoVerification.RustHeap (
  LayoutOk RustAlloc vecHeader vecU8 vecU8At vecU8At_entails_dealloc
)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt speWord)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  DropSpeGhost SatEntails dropSpeStackX invalidMessageStrAt_entails_vecU8 speJumpTable
  spe_strRef_at_8_entails_40 spe_str_words_entails_48 spe_u32x2_at_8_entails_40
  spe_u64_at_8_entails_40 spe_u8_at_32_entails_16 spe_u8_at_8_entails_40
  spe_unit_pre_weaken spe_word8_40_entails_48 strRefAt_entails_memRegion16
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded
)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_553 blkPl_553 lsProg_553)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_lscro)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.IfaceLemmas (withExternStackFromAllocOom')
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofBudget (dropSpeSpecStk)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (
  dealloc_lscro_of_cli lift_stk_lscro_budget
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace Helpers

private abbrev cliSpeJumpTableSym : String :=
  "libsignal_cli:.rodata.core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError>"

private theorem SepWP.false_elim_p {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  have heq : (P ∗ ⌜False⌝ ∗ Q) ∗ R = ⌜False⌝ ∗ (P ∗ Q ∗ R) := by sep_ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact False.elim hm.1

private theorem intro_rodata_cliSpeJumpTable_p [LibsignalPlacement]
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWP prog target_pc s
      ((lsρ cliSpeJumpTableSym ↦ᵣ speJumpTable) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  have hR := h R
  rw [sepConj_assoc] at hR
  exact hR (lsro_intro_chk hro (sym := cliSpeJumpTableSym) (bs := speJumpTable)
    (by decide +kernel) hm)

private theorem cliSpeJumpTable_byte_p (tbl : BitVec 64) (i : Nat) (b : BitVec 8)
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

private theorem stackAt_dropSpeX_split_p (sp : BitVec 64) :
    stackAt sp dropSpeStackX =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

private theorem tail_stack_32_from_bottomX_p (sp : BitVec 64) :
    memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 := by
  rw [show (16416#64 : BitVec 64) = BitVec.ofNat 64 (extHookStack + 32) from rfl,
      ← stackAt_split_bottom sp extHookStack 32 (by decide),
      show extHookStack + 32 = dropSpeStackX from rfl,
      ← stackAt_dropSpeX_split_p sp]

private theorem cells4_entails_stack_bottomX_p (sp : BitVec 64)
    (fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack := by
  rw [tail_stack_32_from_bottomX_p sp]
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))

private theorem stack_restore_32_speX_p (sp fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    stackAt sp dropSpeStackX := by
  rw [stackAt_dropSpeX_split_p sp, ← tail_stack_32_from_bottomX_p sp]
  exact cells4_entails_stack_bottomX_p sp fp lr x20 x19

private theorem spe_str_cap0_budgetX_p (pool : SepProp)
    (a w cap ptr sp fp lr x20 x19 : BitVec 64) (ro : SepProp) :
    SatEntails
      (pool ∗ (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ro ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (spe_str_words_entails_48 a w cap ptr)
  have hst := SatEntails.of_entails (stack_restore_32_speX_p sp fp lr x20 x19)
  refine SatEntails.trans (SatEntails.of_eq (show
    pool ∗ (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
      memRegion (a + 24#64) 24 ∗ ro ∗ stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) =
    ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24) ∗
      ((ro ∗ pool) ∗
       (stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) by sep_ac_rfl)) ?_
  exact SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro hst)

private theorem spe_noop_budgetX_p (pool : SepProp)
    (a w sp fp lr x20 x19 : BitVec 64) (ro : SepProp) :
    SatEntails
      (pool ∗ (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro ∗
        stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (spe_word8_40_entails_48 a w)
  have hst := SatEntails.of_entails (stack_restore_32_speX_p sp fp lr x20 x19)
  refine SatEntails.trans (SatEntails.of_eq (show
    pool ∗ (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro ∗
      stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) =
    ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40) ∗
      ((ro ∗ pool) ∗
       (stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) by sep_ac_rfl)) ?_
  exact SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro hst)

private theorem spe_tail_dealloc_budgetX_p (pool : SepProp)
    (a w cap ptr sp fp lr x20 x19 : BitVec 64) (ro live1 live2 : SepProp) :
    SatEntails
      (pool ∗ (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ro ∗ live1 ∗ live2 ∗
        stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ memRegion (sp - 16416#64) 32 ∗
        stackAt sp extHookStack ∗ (live1 ∗ live2)) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (spe_str_words_entails_48 a w cap ptr)
  have hst := SatEntails.of_entails (cells4_entails_stack_bottomX_p sp fp lr x20 x19)
  refine SatEntails.trans (SatEntails.of_eq (show
    pool ∗ (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
      memRegion (a + 24#64) 24 ∗ ro ∗ live1 ∗ live2 ∗
      stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) =
    ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24) ∗
      ((ro ∗ pool) ∗
       ((stackAt (sp - 32#64) extHookStack ∗
         ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
         ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ∗ (live1 ∗ live2))) by sep_ac_rfl)) ?_
  refine SatEntails.trans
    (SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro (SatEntails.sepConj_mono_left hst))) ?_
  exact SatEntails.of_eq (by sep_ac_rfl)

private theorem spe_tail_dealloc_postX_p (a : BitVec 64) (pool : SepProp) (sp : BitVec 64) :
    pool ∗ stackAt sp extHookStack ∗ memRegion a 48 ∗ memRegion (sp - 16416#64) 32 ⊢
      memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX := by
  rw [stackAt_dropSpeX_split_p sp, ← tail_stack_32_from_bottomX_p sp]
  exact Entails.of_eq (by sep_ac_rfl)

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

private theorem vecU8_at_8_exposeX_p (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (a + 8#64) bs ∗ memRegion (a + 32#64) 16 ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have hexp : vecU8At A (a + 8#64) cap ptr bs ⊢
      ((a + 8#64) ↦₆₄ cap) ∗ ((a + 8#64 + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 8#64 + 16#64) 8 ∗
      (if cap == 0#64 then emp
       else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
    refine Entails.trans (vecU8At_entails_dealloc A (a + 8#64) cap ptr bs) ?_
    unfold vecHeader
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
    have hbeq : ((cap == 0#64) = true) ↔ cap = 0 := beq_iff_eq
    simp only [hbeq]
    rw [sepConj_assoc, sepConj_assoc]
    refine sepConj_mono_right
      (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
    by_cases hc : cap = 0
    · simp only [hc, ↓reduceIte]
      exact Entails.refl _
    · simp only [hc, ↓reduceIte]
      have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun h0 => hc (BitVec.eq_of_toNat_eq h0))
      have hlay : LayoutOk cap.toNat 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
      exact Entails.pure_right hlay (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hexp) ?_
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have h24 : a + 8#64 + 16#64 = a + 24#64 := by bv_omega
  have hm : memRegion (a + 24#64) 24 = memRegion (a + 24#64) 8 ∗ memRegion (a + 32#64) 16 := by
    rw [show (24 : Nat) = 8 + 16 from rfl, memRegion_split (a + 24#64) 8 16 (by decide),
        show a + 24#64 + 8#64 = a + 32#64 by bv_omega]
  rw [h16, h24, hm]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem speAt_invalidState_exposeX_p (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) :
    SatEntails (speAt A fnName a .invalidState)
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  simp only [speAt]
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails.sepExists_elim; intro bs
  refine SatEntails.trans
    (SatEntails.sepConj_mono_right
      (SatEntails.sepConj_mono_right (strRefAt_entails_memRegion16 (a + 32#64) fnName))) ?_
  apply SatEntails.of_entails
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_exposeX_p A a bs)) ?_
  simp only [sepExists_sepConj_right]
  exact Entails.refl _

private theorem speAt_invalidMessage_exposeX_p (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) (t : MessageType) (r : InvalidMessageReason) :
    SatEntails (speAt A fnName a (.invalidMessage t r))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord 24) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  apply SatEntails.of_entails
  simp only [speAt]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (invalidMessageStrAt_entails_vecU8 A (a + 8#64) r)
      (spe_u8_at_32_entails_16 a (msgTypeByte t)))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_exposeX_p A a bs)) ?_
  simp only [sepExists_sepConj_right]
  exact Entails.refl _

private theorem spe_str_pre_weakenX_p (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) {ro_tbl ro_byte : SepProp} (e : SignalProtocolError) (i : Nat) (w : BitVec 64)
    (hw : speWord i = w)
    (hbyte : SatEntails ro_tbl ro_byte)
    (he : SatEntails (speAt A fnName a e)
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord i) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)))
    (rest : SepProp) :
    SatEntails (ro_tbl ∗ (speAt A fnName a e ∗ rest))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ w) ∗
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ro_byte ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ rest) := by
  subst hw
  refine SatEntails.trans (SatEntails.sepConj_mono hbyte (SatEntails.sepConj_mono_left he)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails.sepExists_elim; intro cap
  apply SatEntails.sepExists_elim; intro ptr
  refine SatEntails.sepExists_right cap (SatEntails.sepExists_right ptr ?_)
  exact SatEntails.of_eq (by sep_ac_rfl)

set_option linter.unusedSimpArgs false in
theorem cliDropSpe_placed_ok_x_proof_core [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_553 H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim)) := by
  have hdealloc := dealloc_lscro_of_cli (callerProg := (blkPC_553).rebase (blkPl_553).base H) hA
  unfold withLsCodeRoLoaded dropSpeSpecX
  dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
    withExternStackFromAllocOom', rustCliDeallocBudgetSpec, lsProg_553] at hdealloc ⊢
  change subroutine_ok ((blkPC_553).rebase (blkPl_553).base H) (blkPl_553).base _
  wp_init xs s0
  obtain ⟨⟨a, fnName, e⟩, st⟩ := xs
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = a := by assumption
  subst hx0
  refine intro_rodata_cliSpeJumpTable_p hcrl0.2 ?_
  nth_rw 1 [stackAt_dropSpeX_split_p s0.sp]
  cells_unfold
  wp_pull_exists
  cases e with
  | panic =>
    simp only [speAt]
    exact SepWP.false_elim_p
  | invalidState =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_str_pre_weakenX_p A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidState
        1 0x8000000000000001#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 1 0x00#8 rfl rfl)
        (speAt_invalidState_exposeX_p A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5))) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      simp only [State.setMem_setMem]
      refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
        (spe_str_cap0_budgetX_p _ _ _ _ _ s0.sp _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
      refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hlay1, hlay2, hlay3⟩
      apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      simp only [State.setMem_setMem]
      refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
        (spe_tail_dealloc_budgetX_p _ (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩
      wp_call hdealloc (ptr, cap.toNat, 1, st)
      refine SepWP.weaken_pre
        (spe_tail_dealloc_postX_p (s0.readReg64 (Reg.gpr 0#5)) (A.pool lim _ sf) s0.sp) ?_
      apply SepWP.fold (freeOnlyPool_dealloc A lim st cap.toNat 1 sf) (by sep_focus)
      wp_done
  | invalidMessage t r =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_str_pre_weakenX_p A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidMessage t r)
        24 0x8000000000000018#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 24 0x00#8 rfl rfl)
        (speAt_invalidMessage_exposeX_p A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) t r) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      simp only [State.setMem_setMem]
      refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
        (spe_str_cap0_budgetX_p _ _ _ _ _ s0.sp _ _ _ _ _) ?_
      apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
      refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hlay1, hlay2, hlay3⟩
      apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      simp only [State.setMem_setMem]
      refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
        (spe_tail_dealloc_budgetX_p _ (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩
      wp_call hdealloc (ptr, cap.toNat, 1, st)
      refine SepWP.weaken_pre
        (spe_tail_dealloc_postX_p (s0.readReg64 (Reg.gpr 0#5)) (A.pool lim _ sf) s0.sp) ?_
      apply SepWP.fold (freeOnlyPool_dealloc A lim st cap.toNat 1 sf) (by sep_focus)
      wp_done
  | invalidProtobufEncoding =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidProtobufEncoding
        2 0x8000000000000002#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 2 0x1b#8 rfl rfl)
        (SatEntails.refl _) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budgetX_p _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | ciphertextMessageTooShort n =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.ciphertextMessageTooShort n)
        3 0x8000000000000003#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 3 0x1b#8 rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budgetX_p _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | legacyCiphertextVersion v =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.legacyCiphertextVersion v)
        4 0x8000000000000004#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 4 0x1b#8 rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budgetX_p _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | unrecognizedCiphertextVersion v =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.unrecognizedCiphertextVersion v)
        5 0x8000000000000005#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 5 0x1b#8 rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budgetX_p _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | noKeyTypeIdentifier =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) .noKeyTypeIdentifier
        7 0x8000000000000007#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 7 0x1b#8 rfl rfl)
        (SatEntails.refl _) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budgetX_p _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | badKeyType t =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyType t)
        8 0x8000000000000008#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 8 0x1b#8 rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budgetX_p _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | badKeyLength n =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyLength n)
        9 0x8000000000000009#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 9 0x1b#8 rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budgetX_p _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | invalidKeyAgreement =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidKeyAgreement
        10 0x800000000000000a#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 10 0x1b#8 rfl rfl)
        (SatEntails.refl _) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budgetX_p _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | invalidSessionStructure r =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidSessionStructure r)
        20 0x8000000000000014#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 20 0x1b#8 rfl rfl)
        (by simp only [speAt]; exact SatEntails.sepConj_mono_right (spe_strRef_at_8_entails_40 _ _)) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budgetX_p _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done
  | duplicatedMessage idx c =>
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A.repAlloc fnName (s0.readReg64 (Reg.gpr 0#5)) (.duplicatedMessage idx c)
        23 0x8000000000000017#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 23 0x1b#8 rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u32x2_at_8_entails_40 _ _ _))) _) ?_
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    refine CryptoVerification.LibsignalTripleRatchet.Getters.SepWP.weaken_pre_sat
      (spe_noop_budgetX_p _ _ _ s0.sp _ _ _ _ _) ?_
    apply SepWP.fold (freeOnlyPool_nil A lim st _) (by sep_focus)
    wp_done

end Helpers

theorem cliDropSpe_placed_ok_x_proof [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_553 H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim)) :=
  Helpers.cliDropSpe_placed_ok_x_proof_core hA

theorem cliDropSpe_placed_caller_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 553)
    (cliDropSpe_placed_ok_x_proof hA) hi

def dropSpeSpecStkPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (DropSpeGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (dropSpeSpecStk A lim stk)

private theorem cliDropSpe_placed_ok_stk_base [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_553 H) (lsmpl.base 553)
      (dropSpeSpecStkPlaced A lim dropSpeStackX) := by
  refine subroutine_ok_mono (cliDropSpe_placed_ok_x_proof hA) (fun _ _ _ hp => hp) ?_
  intro ⟨x, st⟩ R s0 sf hq
  dsimp only [dropSpeSpecStkPlaced, withLsCodeRoLoaded, dropSpeSpecStk, dropSpeSpecX] at hq ⊢
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc] at hq ⊢
  rw [satisfies_sepExists] at hq ⊢
  obtain ⟨evs, hevs⟩ := hq
  refine ⟨evs, ?_⟩
  have hevs' : sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗ ⌜FreeOnlyEvs evs⌝ ∗
      (memRegion x.a 48 ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp dropSpeStackX ∗ R) := by
    convert hevs using 1
    sep_ac_rfl
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hevs'
  rw [satisfies_pure_sepConj]
  exact ⟨⟨hevs'.1, hevs'.2.1⟩, by simpa [sepConj_assoc] using hevs'.2.2⟩

theorem cliDropSpe_placed_ok_stk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (_hstk64 : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok (lsProg_553 H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecStk A lim stk)) :=
  lift_stk_lscro_budget (pl := lsmpl) (F := dropSpeSpecStkPlaced A lim)
    (P := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
        speAt A.repAlloc x.fnName x.a x.e ∗ A.pool lim st s)
    (Q := fun (x, st) s0 sf =>
      ∃∗ evs : List AllocEvent,
        ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
          memRegion x.a 48 ∗ A.pool lim (M.stepEvents evs st) sf)
    (cliDropSpe_placed_ok_stk_base hA)
    hstk
    (by
      intro ⟨x, st⟩ s k
      dsimp only [dropSpeSpecStkPlaced, withLsCodeRoLoaded, dropSpeSpecStk]
      sep_ac_rfl)
    (by
      intro ⟨x, st⟩ s0 sf k
      simp only [dropSpeSpecStkPlaced, withLsCodeRoLoaded, dropSpeSpecStk, sepExists_sepConj_left]
      exact sepExists_congr fun _ => by sep_ac_rfl)

theorem cliDropSpe_placed_caller_ok_stk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A lim H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecStk A lim stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 553)
    (cliDropSpe_placed_ok_stk hA stk hstk hstk64) hi

end LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofPlacedBudget
