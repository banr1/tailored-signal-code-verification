/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.Proof
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymA
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common

/-!
# Relocatable `drop_glue::<SignalProtocolError> [local#3]` (Block `552`)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.DropSpeProof

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace Helpers

private abbrev cliSpeJumpTableSym : String :=
  "libsignal_cli:.rodata.core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError>"

private def SatEntailsP (P Q : SepProp) : Prop :=
  ∀ (m : Memory) (R : SepProp), (m ⊨ P ∗ R) → (m ⊨ Q ∗ R)

private theorem SatEntailsP.refl (P : SepProp) : SatEntailsP P P :=
  fun _ _ hm => hm

private theorem SatEntailsP.of_eq {P Q : SepProp} (h : P = Q) : SatEntailsP P Q :=
  h ▸ SatEntailsP.refl P

private theorem SatEntailsP.of_entails {P Q : SepProp} (h : P ⊢ Q) : SatEntailsP P Q :=
  fun _ _ hm => Satisfies.mono (sepConj_mono_left h) hm

private theorem SatEntailsP.trans {P Q S : SepProp}
    (h1 : SatEntailsP P Q) (h2 : SatEntailsP Q S) : SatEntailsP P S :=
  fun m R hm => h2 m R (h1 m R hm)

private theorem SatEntailsP.drop_left (P Q : SepProp) : SatEntailsP (P ∗ Q) Q := by
  intro m R hm
  rw [sepConj_assoc] at hm
  exact Satisfies.of_sep_right hm

private theorem SatEntailsP.drop_right (P Q : SepProp) : SatEntailsP (P ∗ Q) P := by
  intro m R hm
  rw [sepConj_comm P Q, sepConj_assoc] at hm
  exact Satisfies.of_sep_right hm

private theorem SatEntailsP.sepConj_mono {P₁ P₂ Q₁ Q₂ : SepProp}
    (h1 : SatEntailsP P₁ P₂) (h2 : SatEntailsP Q₁ Q₂) :
    SatEntailsP (P₁ ∗ Q₁) (P₂ ∗ Q₂) := by
  intro m R hm
  rw [sepConj_assoc] at hm
  have hm1 := h1 m (Q₁ ∗ R) hm
  rw [← sepConj_assoc, sepConj_comm P₂ Q₁, sepConj_assoc] at hm1
  have hm2 := h2 m (P₂ ∗ R) hm1
  rw [← sepConj_assoc, sepConj_comm Q₂ P₂] at hm2
  exact hm2

private theorem SatEntailsP.sepConj_mono_left {P₁ P₂ : SepProp}
    (h : SatEntailsP P₁ P₂) {Q : SepProp} : SatEntailsP (P₁ ∗ Q) (P₂ ∗ Q) :=
  SatEntailsP.sepConj_mono h (SatEntailsP.refl Q)

private theorem SatEntailsP.sepConj_mono_right {P Q₁ Q₂ : SepProp}
    (h : SatEntailsP Q₁ Q₂) : SatEntailsP (P ∗ Q₁) (P ∗ Q₂) :=
  SatEntailsP.sepConj_mono (SatEntailsP.refl P) h

private theorem SatEntailsP.sepExists_elim {α : Type} {P : α → SepProp} {Q : SepProp}
    (h : ∀ x, SatEntailsP (P x) Q) : SatEntailsP (∃∗ x, P x) Q := by
  intro m R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x m R hx

private theorem SatEntailsP.sepExists_right {α : Type} {P : SepProp} {Q : α → SepProp}
    (x : α) (h : SatEntailsP P (Q x)) : SatEntailsP P (∃∗ y, Q y) :=
  SatEntailsP.trans h (SatEntailsP.of_entails (Entails.sepExists_right x (Entails.refl _)))

private theorem SepWP.weaken_pre_satP {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (himp : SatEntailsP P P')
    (h : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  exact h R (himp s.mem R hm)

private theorem SepWP.intro_rodata_cliSpeJumpTable_p [LibsignalPlacement]
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

private theorem strRefAt_entails_memRegion16_p (a : BitVec 64) (lit : List (BitVec 8)) :
    SatEntailsP (strRefAt a lit) (memRegion a 16) := by
  unfold strRefAt
  apply SatEntailsP.sepExists_elim
  intro p
  refine SatEntailsP.trans (SatEntailsP.sepConj_mono_right (SatEntailsP.drop_right _ _)) ?_
  apply SatEntailsP.of_entails
  rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split a 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a p)
    (pointsTo64_entails_memRegion (a + 8#64) _)

private theorem spe_word8_40_entails_48_p (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ⊢ memRegion a 48 := by
  rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split a 8 40 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a w)

private theorem spe_u64_at_8_entails_40_p (a : BitVec 64) (v : BitVec 64) :
    ((a + 8#64) ↦₆₄ v) ∗ memRegion (a + 16#64) 32 ⊢ memRegion (a + 8#64) 40 := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 := by
    rw [show (40 : Nat) = 8 + 32 from rfl, memRegion_split (a + 8#64) 8 32 (by decide),
        show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (a + 8#64) v)

private theorem spe_u8_at_8_entails_40_p (a : BitVec 64) (v : BitVec 8) :
    ((a + 8#64) ↦₈ v) ∗ memRegion (a + 9#64) 39 ⊢ memRegion (a + 8#64) 40 := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 1 ∗ memRegion (a + 9#64) 39 := by
    rw [show (40 : Nat) = 1 + 39 from rfl, memRegion_split (a + 8#64) 1 39 (by decide),
        show a + 8#64 + 1#64 = a + 9#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left
    (IsBlock.entails (IsBlock.pointsTo8 (a + 8#64) v) (IsBlock.memRegion (a + 8#64) 1)
      fun _ _ => trivial)

private theorem spe_u8_at_32_entails_16_p (a : BitVec 64) (v : BitVec 8) :
    ((a + 32#64) ↦₈ v) ∗ memRegion (a + 33#64) 15 ⊢ memRegion (a + 32#64) 16 := by
  have h : memRegion (a + 32#64) 16 = memRegion (a + 32#64) 1 ∗ memRegion (a + 33#64) 15 := by
    rw [show (16 : Nat) = 1 + 15 from rfl, memRegion_split (a + 32#64) 1 15 (by decide),
        show a + 32#64 + 1#64 = a + 33#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left
    (IsBlock.entails (IsBlock.pointsTo8 (a + 32#64) v) (IsBlock.memRegion (a + 32#64) 1)
      fun _ _ => trivial)

private theorem spe_u32x2_at_8_entails_40_p (a : BitVec 64) (v1 v2 : BitVec 32) :
    ((a + 8#64) ↦₃₂ v1) ∗ ((a + 12#64) ↦₃₂ v2) ∗ memRegion (a + 16#64) 32 ⊢
      memRegion (a + 8#64) 40 := by
  have h1 : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 4 ∗ memRegion (a + 12#64) 36 := by
    rw [show (40 : Nat) = 4 + 36 from rfl, memRegion_split (a + 8#64) 4 36 (by decide),
        show a + 8#64 + 4#64 = a + 12#64 by bv_omega]
  have h2 : memRegion (a + 12#64) 36 = memRegion (a + 12#64) 4 ∗ memRegion (a + 16#64) 32 := by
    rw [show (36 : Nat) = 4 + 32 from rfl, memRegion_split (a + 12#64) 4 32 (by decide),
        show a + 12#64 + 4#64 = a + 16#64 by bv_omega]
  rw [h1, h2]
  exact sepConj_mono
    (IsBlock.entails (IsBlock.pointsTo32 (a + 8#64) v1) (IsBlock.memRegion (a + 8#64) 4)
      fun _ _ => trivial)
    (sepConj_mono_left
      (IsBlock.entails (IsBlock.pointsTo32 (a + 12#64) v2) (IsBlock.memRegion (a + 12#64) 4)
        fun _ _ => trivial))

private theorem spe_strRef_at_8_entails_40_p (a : BitVec 64) (lit : List (BitVec 8)) :
    SatEntailsP (strRefAt (a + 8#64) lit ∗ memRegion (a + 24#64) 24) (memRegion (a + 8#64) 40) := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 16 ∗ memRegion (a + 24#64) 24 := by
    rw [show (40 : Nat) = 16 + 24 from rfl, memRegion_split (a + 8#64) 16 24 (by decide),
        show a + 8#64 + 16#64 = a + 24#64 by bv_omega]
  rw [h]
  exact SatEntailsP.sepConj_mono_left (strRefAt_entails_memRegion16_p (a + 8#64) lit)

private theorem spe_str_words_entails_48_p (a w cap ptr : BitVec 64) :
    (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ⊢
      memRegion a 48 := by
  have h1 : memRegion a 48 = memRegion a 8 ∗ memRegion (a + 8#64) 40 := by
    rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split a 8 40 (by decide)]
  have h2 : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 := by
    rw [show (40 : Nat) = 8 + 32 from rfl, memRegion_split (a + 8#64) 8 32 (by decide),
        show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  have h3 : memRegion (a + 16#64) 32 = memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 24 := by
    rw [show (32 : Nat) = 8 + 24 from rfl, memRegion_split (a + 16#64) 8 24 (by decide),
        show a + 16#64 + 8#64 = a + 24#64 by bv_omega]
  rw [h1, h2, h3]
  exact sepConj_mono (pointsTo64_entails_memRegion a w)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) cap)
      (sepConj_mono_left (pointsTo64_entails_memRegion (a + 16#64) ptr)))

private theorem spe_str_cap0_pre_weaken_p (a w cap ptr : BitVec 64) (ro pool rest : SepProp) :
    SatEntailsP
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ pool ∗ rest)
      (memRegion a 48 ∗ pool ∗ rest) := by
  have hro : SatEntailsP (ro ∗ pool) pool := SatEntailsP.drop_left ro pool
  have ha := SatEntailsP.of_entails (spe_str_words_entails_48_p a w cap ptr)
  have hreord :
      (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ pool ∗ rest =
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24) ∗
        ((ro ∗ pool) ∗ rest) := by ac_rfl
  rw [hreord]
  exact SatEntailsP.sepConj_mono ha (SatEntailsP.sepConj_mono_left hro)

private theorem spe_noop_pre_weaken_p (a w : BitVec 64) (ro pool rest : SepProp) :
    SatEntailsP
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro ∗ pool ∗ rest)
      (memRegion a 48 ∗ pool ∗ rest) := by
  have hro : SatEntailsP (ro ∗ pool) pool := SatEntailsP.drop_left ro pool
  have ha := SatEntailsP.of_entails (spe_word8_40_entails_48_p a w)
  have hreord :
      (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro ∗ pool ∗ rest =
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40) ∗ ((ro ∗ pool) ∗ rest) := by ac_rfl
  rw [hreord]
  exact SatEntailsP.sepConj_mono ha (SatEntailsP.sepConj_mono_left hro)

private theorem invalidMessageStrAt_entails_vecU8_p (A : RustAlloc) (a : BitVec 64)
    (r : InvalidMessageReason) :
    invalidMessageStrAt A a r ⊢ ∃∗ bs : List (BitVec 8), vecU8 A a bs := by
  cases r with
  | tooFarInFuture =>
    simp only [invalidMessageStrAt]
    exact Entails.sepExists_right tooFarInFutureStr (Entails.refl _)
  | macFailed =>
    simp only [invalidMessageStrAt]
    exact Entails.sepExists_right macFailedStr (Entails.refl _)
  | pqRatchet =>
    simp only [invalidMessageStrAt]
    exact Entails.refl _
  | badCiphertext =>
    simp only [invalidMessageStrAt]
    exact Entails.refl _
  | decryptionFailed =>
    simp only [invalidMessageStrAt]
    rw [← sepConj_emp ⌜False⌝]
    exact Entails.pure_left nofun

private theorem spe_unit_pre_weaken_p (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) {ro_tbl ro_byte : SepProp} (e : SignalProtocolError) (i : Nat) (w : BitVec 64)
    (hw : speWord i = w)
    (hbyte : SatEntailsP ro_tbl ro_byte)
    (he : SatEntailsP (speAt A fnName a e) ((a ↦₆₄ speWord i) ∗ memRegion (a + 8#64) 40))
    (rest : SepProp) :
    SatEntailsP (ro_tbl ∗ (speAt A fnName a e ∗ rest))
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro_byte ∗ rest) := by
  subst hw
  refine SatEntailsP.trans (SatEntailsP.sepConj_mono hbyte (SatEntailsP.sepConj_mono_left he)) ?_
  exact SatEntailsP.of_eq (by ac_rfl)

private theorem SepWP.false_elim_p {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  have heq : (P ∗ ⌜False⌝ ∗ Q) ∗ R = ⌜False⌝ ∗ (P ∗ Q ∗ R) := by ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact False.elim hm.1

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

private theorem spe_str_cap0_pre_weaken_fullX_p (a w cap ptr sp fp lr x20 x19 : BitVec 64)
    (ro pool : SepProp) :
    SatEntailsP
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) :=
  SatEntailsP.trans (spe_str_cap0_pre_weaken_p a w cap ptr ro pool _)
    (SatEntailsP.of_entails
      (sepConj_mono_right (sepConj_mono_right (stack_restore_32_speX_p sp fp lr x20 x19))))

private theorem spe_noop_pre_weaken_fullX_p (a w sp fp lr x20 x19 : BitVec 64)
    (ro pool : SepProp) :
    SatEntailsP
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) :=
  SatEntailsP.trans (spe_noop_pre_weaken_p a w ro pool _)
    (SatEntailsP.of_entails
      (sepConj_mono_right (sepConj_mono_right (stack_restore_32_speX_p sp fp lr x20 x19))))

private theorem spe_tail_dealloc_pre_weakenX_p (a w cap ptr sp : BitVec 64)
    (fp lr x20 x19 : BitVec 64) (ro live1 live2 pool : SepProp) :
    SatEntailsP
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ live1 ∗ live2 ∗ pool ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack ∗
        (live1 ∗ live2)) := by
  have hro : SatEntailsP (ro ∗ pool) pool := SatEntailsP.drop_left ro pool
  have ha := SatEntailsP.of_entails (spe_str_words_entails_48_p a w cap ptr)
  have hst := SatEntailsP.of_entails (cells4_entails_stack_bottomX_p sp fp lr x20 x19)
  have hreord :
      (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ live1 ∗ live2 ∗ pool ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) =
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24) ∗
        ((ro ∗ pool) ∗
         ((stackAt (sp - 32#64) extHookStack ∗
           ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
           ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ∗ (live1 ∗ live2))) := by ac_rfl
  rw [hreord]
  refine SatEntailsP.trans
    (SatEntailsP.sepConj_mono ha (SatEntailsP.sepConj_mono hro (SatEntailsP.sepConj_mono_left hst))) ?_
  exact SatEntailsP.of_eq (by ac_rfl)

private theorem spe_tail_dealloc_postX_p (a : BitVec 64) (pool : SepProp) (sp : BitVec 64) :
    pool ∗ stackAt sp extHookStack ∗ memRegion a 48 ∗ memRegion (sp - 16416#64) 32 ⊢
      memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX := by
  rw [stackAt_dropSpeX_split_p sp, ← tail_stack_32_from_bottomX_p sp]
  exact Entails.of_eq (by ac_rfl)

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
  exact Entails.of_eq (by ac_rfl)

private theorem speAt_invalidState_exposeX_p (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) :
    SatEntailsP (speAt A fnName a .invalidState)
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  simp only [speAt]
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntailsP.sepExists_elim; intro bs
  refine SatEntailsP.trans
    (SatEntailsP.sepConj_mono_right
      (SatEntailsP.sepConj_mono_right (strRefAt_entails_memRegion16_p (a + 32#64) fnName))) ?_
  apply SatEntailsP.of_entails
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_exposeX_p A a bs)) ?_
  simp only [sepExists_sepConj_right]
  exact Entails.refl _

private theorem speAt_invalidMessage_exposeX_p (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) (t : MessageType) (r : InvalidMessageReason) :
    SatEntailsP (speAt A fnName a (.invalidMessage t r))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord 24) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  apply SatEntailsP.of_entails
  simp only [speAt]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (invalidMessageStrAt_entails_vecU8_p A (a + 8#64) r)
      (spe_u8_at_32_entails_16_p a (msgTypeByte t)))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_exposeX_p A a bs)) ?_
  simp only [sepExists_sepConj_right]
  exact Entails.refl _

private theorem spe_str_pre_weakenX_p (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) {ro_tbl ro_byte : SepProp} (e : SignalProtocolError) (i : Nat) (w : BitVec 64)
    (hw : speWord i = w)
    (hbyte : SatEntailsP ro_tbl ro_byte)
    (he : SatEntailsP (speAt A fnName a e)
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord i) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)))
    (rest : SepProp) :
    SatEntailsP (ro_tbl ∗ (speAt A fnName a e ∗ rest))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ w) ∗
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ro_byte ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ rest) := by
  subst hw
  refine SatEntailsP.trans (SatEntailsP.sepConj_mono hbyte (SatEntailsP.sepConj_mono_left he)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntailsP.sepExists_elim; intro cap
  apply SatEntailsP.sepExists_elim; intro ptr
  refine SatEntailsP.sepExists_right cap (SatEntailsP.sepExists_right ptr ?_)
  exact SatEntailsP.of_eq (by ac_rfl)

set_option linter.unusedSimpArgs false in
theorem cliDropSpe_placed_ok_x_proof_core [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_553 H) (lsmpl.base 553)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecX A)) := by
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_553 H) hA
  unfold StoreKit.withLsCodeRoLoaded dropSpeSpecX
  dsimp only [StoreKit.withLsCodeRoLoaded, rustDeallocExternSpecWithStack, lsProg_553] at hdealloc ⊢
  change subroutine_ok ((blkPC_553).rebase (blkPl_553).base H) (blkPl_553).base _
  wp_init x s0
  obtain ⟨a, fnName, e⟩ := x
  dsimp only at *
  have hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = a := by assumption
  subst hx0
  refine SepWP.intro_rodata_cliSpeJumpTable_p hcrl0.2 ?_
  nth_rw 1 [stackAt_dropSpeX_split_p s0.sp]
  cells_unfold
  wp_pull_exists
  cases e with
  | panic =>
    simp only [speAt]
    exact SepWP.false_elim_p
  | invalidState =>
    refine SepWP.weaken_pre_satP
      (spe_str_pre_weakenX_p A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidState
        1 0x8000000000000001#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 1 0x00#8 rfl rfl)
        (speAt_invalidState_exposeX_p A fnName (s0.readReg64 (Reg.gpr 0#5))) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine SepWP.weaken_pre_satP (spe_str_cap0_pre_weaken_fullX_p _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hlay1, hlay2, hlay3⟩
      apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps
      refine SepWP.weaken_pre_satP
        (spe_tail_dealloc_pre_weakenX_p (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩
      wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX_p (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done
  | invalidMessage t r =>
    refine SepWP.weaken_pre_satP
      (spe_str_pre_weakenX_p A fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidMessage t r)
        24 0x8000000000000018#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 24 0x00#8 rfl rfl)
        (speAt_invalidMessage_exposeX_p A fnName (s0.readReg64 (Reg.gpr 0#5)) t r) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine SepWP.weaken_pre_satP (spe_str_cap0_pre_weaken_fullX_p _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hlay1, hlay2, hlay3⟩
      apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl0
      wp_steps
      refine SepWP.weaken_pre_satP
        (spe_tail_dealloc_pre_weakenX_p (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_t, hro_t⟩
      wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX_p (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done
  | invalidProtobufEncoding =>
    refine SepWP.weaken_pre_satP
      (spe_unit_pre_weaken_p A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidProtobufEncoding
        2 0x8000000000000002#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 2 0x1b#8 rfl rfl)
        (SatEntailsP.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_satP (spe_noop_pre_weaken_fullX_p _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | ciphertextMessageTooShort n =>
    refine SepWP.weaken_pre_satP
      (spe_unit_pre_weaken_p A fnName (s0.readReg64 (Reg.gpr 0#5)) (.ciphertextMessageTooShort n)
        3 0x8000000000000003#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 3 0x1b#8 rfl rfl)
        (SatEntailsP.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40_p _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_satP (spe_noop_pre_weaken_fullX_p _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | legacyCiphertextVersion v =>
    refine SepWP.weaken_pre_satP
      (spe_unit_pre_weaken_p A fnName (s0.readReg64 (Reg.gpr 0#5)) (.legacyCiphertextVersion v)
        4 0x8000000000000004#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 4 0x1b#8 rfl rfl)
        (SatEntailsP.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40_p _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_satP (spe_noop_pre_weaken_fullX_p _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | unrecognizedCiphertextVersion v =>
    refine SepWP.weaken_pre_satP
      (spe_unit_pre_weaken_p A fnName (s0.readReg64 (Reg.gpr 0#5)) (.unrecognizedCiphertextVersion v)
        5 0x8000000000000005#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 5 0x1b#8 rfl rfl)
        (SatEntailsP.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40_p _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_satP (spe_noop_pre_weaken_fullX_p _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | noKeyTypeIdentifier =>
    refine SepWP.weaken_pre_satP
      (spe_unit_pre_weaken_p A fnName (s0.readReg64 (Reg.gpr 0#5)) .noKeyTypeIdentifier
        7 0x8000000000000007#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 7 0x1b#8 rfl rfl)
        (SatEntailsP.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_satP (spe_noop_pre_weaken_fullX_p _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | badKeyType t =>
    refine SepWP.weaken_pre_satP
      (spe_unit_pre_weaken_p A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyType t)
        8 0x8000000000000008#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 8 0x1b#8 rfl rfl)
        (SatEntailsP.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40_p _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_satP (spe_noop_pre_weaken_fullX_p _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | badKeyLength n =>
    refine SepWP.weaken_pre_satP
      (spe_unit_pre_weaken_p A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyLength n)
        9 0x8000000000000009#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 9 0x1b#8 rfl rfl)
        (SatEntailsP.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40_p _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_satP (spe_noop_pre_weaken_fullX_p _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | invalidKeyAgreement =>
    refine SepWP.weaken_pre_satP
      (spe_unit_pre_weaken_p A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidKeyAgreement
        10 0x800000000000000a#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 10 0x1b#8 rfl rfl)
        (SatEntailsP.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_satP (spe_noop_pre_weaken_fullX_p _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | invalidSessionStructure r =>
    refine SepWP.weaken_pre_satP
      (spe_unit_pre_weaken_p A fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidSessionStructure r)
        20 0x8000000000000014#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 20 0x1b#8 rfl rfl)
        (by simp only [speAt]; exact SatEntailsP.sepConj_mono_right (spe_strRef_at_8_entails_40_p _ _)) _) ?_
    wp_steps
    refine SepWP.weaken_pre_satP (spe_noop_pre_weaken_fullX_p _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | duplicatedMessage idx c =>
    refine SepWP.weaken_pre_satP
      (spe_unit_pre_weaken_p A fnName (s0.readReg64 (Reg.gpr 0#5)) (.duplicatedMessage idx c)
        23 0x8000000000000017#64 rfl
        (cliSpeJumpTable_byte_p (lsρ cliSpeJumpTableSym) 23 0x1b#8 rfl rfl)
        (SatEntailsP.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u32x2_at_8_entails_40_p _ _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_satP (spe_noop_pre_weaken_fullX_p _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done

end Helpers

theorem cliDropSpe_placed_ok_x_proof [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_553 H) (lsmpl.base 553)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecX A)) :=
  Helpers.cliDropSpe_placed_ok_x_proof_core hA

theorem cliDropSpe_placed_caller_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A H) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 553)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecX A)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 553)
    (cliDropSpe_placed_ok_x_proof hA) hi

def dropSpeSpecStkPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) : Spec DropSpeGhost :=
  StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecStk A stk)

theorem cliDropSpe_placed_ok_stk [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_553 H) (lsmpl.base 553)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecStk A stk)) := by
  have hstkX : dropSpeStackX ≤ stk := hstk
  refine Helpers.subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - dropSpeStackX))
    (cliDropSpe_placed_ok_x_proof hA)
    (fun _ s0 => ?_)
    (fun _ s0 _ => ?_)
    (fun _ _ _ => ?_)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)
  · dsimp only [StoreKit.withLsCodeRoLoaded]
    simp only [dropSpeSpecStk, dropSpeSpecX, Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [StoreKit.withLsCodeRoLoaded]
    simp only [dropSpeSpecStk, dropSpeSpecX, Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [StoreKit.withLsCodeRoLoaded]
    exact Entails.pure_left nofun

theorem cliDropSpe_placed_caller_ok_stk [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A H)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 553)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecStk A stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 553)
    (cliDropSpe_placed_ok_stk hA stk hstk hstk64) hi

end CryptoVerification.SignalSession.Cli.DropSpeProof
