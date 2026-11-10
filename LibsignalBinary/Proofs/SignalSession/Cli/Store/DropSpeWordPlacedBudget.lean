/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWordPlaced
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common

/-!
# Budget-Threaded Relocatable `drop_glue::<SignalProtocolError>`

Proves budget-threaded `dropSpeWordSpecPlaced` on Block `553` (`lsProg_553 H`) under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWordPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement LibsignalRoLoaded lsmpl lsro_intro_chk lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropSpeStackX speJumpTable)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_553 blkPl_553 lsProg_553)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_lscro)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced dropSpeWordSpecPlaced)

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private abbrev cliSpeJumpTableSym : String :=
  "libsignal_cli:.rodata.core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError>"

private def SatEntailsP (P Q : SepProp) : Prop :=
  ∀ m R, (m ⊨ P ∗ R) → (m ⊨ Q ∗ R)

private theorem SatEntailsP.of_eq {P Q : SepProp} (h : P = Q) : SatEntailsP P Q :=
  h ▸ fun _ _ hm => hm

private theorem SatEntailsP.of_entails {P Q : SepProp} (h : P ⊢ Q) : SatEntailsP P Q :=
  fun _ _R hm => Satisfies.mono (sepConj_mono_left h) hm

private theorem SatEntailsP.trans {P Q S : SepProp}
    (h1 : SatEntailsP P Q) (h2 : SatEntailsP Q S) : SatEntailsP P S :=
  fun m R hm => h2 m R (h1 m R hm)

private theorem SatEntailsP.drop_left (P Q : SepProp) : SatEntailsP (P ∗ Q) Q := by
  intro m R hm
  rw [sepConj_assoc] at hm
  exact Satisfies.drop_left hm

private theorem SatEntailsP.drop_right (P Q : SepProp) : SatEntailsP (P ∗ Q) P := by
  rw [sepConj_comm]
  exact SatEntailsP.drop_left Q P

private theorem SatEntailsP.sepConj_mono {P1 Q1 P2 Q2 : SepProp}
    (h1 : SatEntailsP P1 Q1) (h2 : SatEntailsP P2 Q2) :
    SatEntailsP (P1 ∗ P2) (Q1 ∗ Q2) := by
  intro m R hm
  rw [sepConj_assoc] at hm
  have hm1 := h1 m (P2 ∗ R) hm
  rw [show Q1 ∗ (P2 ∗ R) = P2 ∗ (Q1 ∗ R) by sep_ac_rfl] at hm1
  have hm2 := h2 m (Q1 ∗ R) hm1
  rwa [show Q2 ∗ (Q1 ∗ R) = (Q1 ∗ Q2) ∗ R by sep_ac_rfl] at hm2

private theorem SatEntailsP.sepConj_mono_left {P Q S : SepProp}
    (h : SatEntailsP P Q) : SatEntailsP (P ∗ S) (Q ∗ S) :=
  SatEntailsP.sepConj_mono h (SatEntailsP.of_eq rfl)

private theorem SepWP.weaken_pre_satP {prog : Program} {target_pc : BitVec 64}
    {s : State} {P Q : SepProp} {post : State → SepProp → Prop}
    (himp : SatEntailsP P Q) (h : SepWP prog target_pc s Q post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  exact h R (himp s.mem R hm)

private theorem SepWP.intro_rodata_cliSpeJumpTable_placed [LibsignalPlacement]
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

private theorem cliSpeJumpTable_byte_placed (tbl : BitVec 64) (i : Nat) (b : BitVec 8)
    (heq : speJumpTable = speJumpTable.take i ++ (b :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i) :
    SatEntailsP (tbl ↦ᵣ speJumpTable) ((tbl + BitVec.ofNat 64 i) ↦₈ᵣ b) := by
  have h :
      (tbl ↦ᵣ speJumpTable) =
      (tbl ↦ᵣ speJumpTable.take i) ∗
        (((tbl + BitVec.ofNat 64 i) ↦₈ᵣ b) ∗
         ((tbl + BitVec.ofNat 64 i + 1#64) ↦ᵣ speJumpTable.drop (i + 1))) := by
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen]
  rw [h]
  exact SatEntailsP.trans (SatEntailsP.drop_left _ _) (SatEntailsP.drop_right _ _)

private theorem stackAt_dropSpeX_split_placed (sp : BitVec 64) :
    stackAt sp dropSpeStackX =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

private theorem stack_restore_32_speX_placed (sp fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    stackAt sp dropSpeStackX := by
  rw [stackAt_dropSpeX_split_placed sp]
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))

private theorem spe_word8_40_entails_48_placed (a w : BitVec 64) :
    (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ⊢ memRegion a 48 := by
  rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split a 8 40 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a w)

private theorem spe_word_pre_weaken_placed (a : BitVec 64) {ro_tbl ro_byte : SepProp}
    (i : Nat) (w : BitVec 64) (hw : speWord i = w)
    (hbyte : SatEntailsP ro_tbl ro_byte) (rest : SepProp) :
    SatEntailsP (ro_tbl ∗ ((a ↦₆₄ speWord i) ∗ rest))
      ((a ↦₆₄ w) ∗ ro_byte ∗ rest) := by
  subst hw
  refine SatEntailsP.trans (SatEntailsP.sepConj_mono_left hbyte) ?_
  exact SatEntailsP.of_eq (by sep_ac_rfl)

private theorem spe_word_post_weaken_placed (a w sp fp lr x20 x19 : BitVec 64)
    (ro pool : SepProp) :
    SatEntailsP
      (pool ∗ (a ↦₆₄ w) ∗ ro ∗ memRegion (a + 8#64) 40 ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) := by
  have hro : SatEntailsP (ro ∗ pool) pool := SatEntailsP.drop_left ro pool
  have ha := SatEntailsP.of_entails (spe_word8_40_entails_48_placed a w)
  have hst := SatEntailsP.of_entails (stack_restore_32_speX_placed sp fp lr x20 x19)
  have hreord :
      pool ∗ (a ↦₆₄ w) ∗ ro ∗ memRegion (a + 8#64) 40 ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40) ∗
        ((ro ∗ pool) ∗
          (stackAt (sp - 32#64) extHookStack ∗
            ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
            ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by sep_ac_rfl
  rw [hreord]
  exact SatEntailsP.sepConj_mono ha (SatEntailsP.sepConj_mono hro hst)

/-- Block `552` (`drop_glue::<SignalProtocolError>`) meets `dropSpeWordSpecPlaced A lim`. -/
theorem dropSpeWord_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (_hA : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_553 H) (lsmpl.base 553) (dropSpeWordSpecPlaced A lim) := by
  unfold dropSpeWordSpecPlaced withLsCodeRoLoaded
  dsimp only [lsProg_553]
  change subroutine_ok ((blkPC_553).rebase (blkPl_553).base H) (blkPl_553).base _
  wp_init xs s0
  obtain ⟨⟨a, w⟩, st⟩ := xs
  dsimp only at *
  have hcrl : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have ha : s0.readReg64 (Reg.gpr 0#5) = a := by assumption
  have hw : w = 13 ∨ w = 14 := by assumption
  subst ha
  refine SepWP.intro_rodata_cliSpeJumpTable_placed hcrl.2 ?_
  nth_rw 1 [stackAt_dropSpeX_split_placed s0.sp]
  cells_unfold
  wp_pull_exists
  rcases hw with rfl | rfl
  · refine SepWP.weaken_pre_satP
      (spe_word_pre_weaken_placed (s0.readReg64 (Reg.gpr 0#5))
        13 0x800000000000000d#64 rfl
        (cliSpeJumpTable_byte_placed (lsρ cliSpeJumpTableSym) 13 0x1b#8 rfl rfl) _) ?_
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    refine SepWP.weaken_pre_satP (spe_word_post_weaken_placed _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  · refine SepWP.weaken_pre_satP
      (spe_word_pre_weaken_placed (s0.readReg64 (Reg.gpr 0#5))
        14 0x800000000000000e#64 rfl
        (cliSpeJumpTable_byte_placed (lsρ cliSpeJumpTableSym) 14 0x1b#8 rfl rfl) _) ?_
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    refine SepWP.weaken_pre_satP (spe_word_post_weaken_placed _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done

theorem dropSpeWord_placed_caller_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsXCliPlaced A lim H)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 553) (dropSpeWordSpecPlaced A lim) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 553) (dropSpeWord_placed_ok hA) hblk

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWordPlacedBudget
