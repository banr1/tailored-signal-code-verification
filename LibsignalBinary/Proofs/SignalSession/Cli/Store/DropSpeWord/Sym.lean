/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.Entry

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.DropSpeWord.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?

gen_decodes CryptoVerification.libsignalSessionCode_tree cliDropSpeWordBin
  [(ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]") →
   (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 180)]

private def SatEntails (P Q : SepProp) : Prop :=
  ∀ (m : Memory) (R : SepProp), (m ⊨ P ∗ R) → (m ⊨ Q ∗ R)

private theorem SatEntails.refl (P : SepProp) : SatEntails P P :=
  fun _ _ hm => hm

private theorem SatEntails.of_eq {P Q : SepProp} (h : P = Q) : SatEntails P Q :=
  h ▸ SatEntails.refl P

private theorem SatEntails.of_entails {P Q : SepProp} (h : P ⊢ Q) : SatEntails P Q :=
  fun _ _ hm => Satisfies.mono (sepConj_mono_left h) hm

private theorem SatEntails.trans {P Q S : SepProp}
    (h1 : SatEntails P Q) (h2 : SatEntails Q S) : SatEntails P S :=
  fun m R hm => h2 m R (h1 m R hm)

private theorem SatEntails.drop_left (P Q : SepProp) : SatEntails (P ∗ Q) Q := by
  intro m R hm
  rw [sepConj_assoc] at hm
  exact Satisfies.of_sep_right hm

private theorem SatEntails.drop_right (P Q : SepProp) : SatEntails (P ∗ Q) P := by
  intro m R hm
  rw [sepConj_comm P Q, sepConj_assoc] at hm
  exact Satisfies.of_sep_right hm

private theorem SatEntails.sepConj_mono {P₁ P₂ Q₁ Q₂ : SepProp}
    (h1 : SatEntails P₁ P₂) (h2 : SatEntails Q₁ Q₂) :
    SatEntails (P₁ ∗ Q₁) (P₂ ∗ Q₂) := by
  intro m R hm
  rw [sepConj_assoc] at hm
  have hm1 := h1 m (Q₁ ∗ R) hm
  rw [← sepConj_assoc, sepConj_comm P₂ Q₁, sepConj_assoc] at hm1
  have hm2 := h2 m (P₂ ∗ R) hm1
  rw [← sepConj_assoc, sepConj_comm Q₂ P₂] at hm2
  exact hm2

private theorem SatEntails.sepConj_mono_left {P₁ P₂ : SepProp}
    (h : SatEntails P₁ P₂) {Q : SepProp} : SatEntails (P₁ ∗ Q) (P₂ ∗ Q) :=
  SatEntails.sepConj_mono h (SatEntails.refl Q)

private theorem SepWP.weaken_pre_sat {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (himp : SatEntails P P')
    (h : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  exact h R (himp s.mem R hm)

private theorem rodata_cliSpeJumpTable_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44)) -
       num% (ls_field% dataOff))).take 28 = speJumpTable := by
  rfl_kernel

private theorem rodata_cliSpeJumpTable_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44))) ↦ᵣ
        speJumpTable) ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (dataOff := num% (ls_field% dataOff)) rfl
    (secOff := num% (ls_xref%
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44)))
    (secLen := 28)
    (List.mem_of_elem_eq_true (by rfl_kernel))
    (Nat.le_of_ble_eq_true (by rfl_kernel))
    (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel))
    (by rfl_kernel) hro hP
  rwa [rodata_cliSpeJumpTable_eq] at h

private theorem SepWP.intro_rodata_cliSpeJumpTable {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hro : img.RoDataLoaded s.mem)
    (h : SepWP prog target_pc s
      (((img.base + bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44))) ↦ᵣ
        speJumpTable) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  have hR := h R
  rw [sepConj_assoc] at hR
  exact hR (rodata_cliSpeJumpTable_intro himg hro hm)

private theorem cliSpeJumpTable_byte (base : BitVec 64) (i : Nat) (off : BitVec 64) (b : BitVec 8)
    (hoff : bv% (ls_xref%
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44)) +
      BitVec.ofNat 64 i = off)
    (heq : speJumpTable = speJumpTable.take i ++ (b :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i) :
    SatEntails
      ((base + bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44))) ↦ᵣ
        speJumpTable)
      ((base + off) ↦₈ᵣ b) := by
  have h :
      ((base + bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44))) ↦ᵣ
        speJumpTable) =
      ((base + bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44))) ↦ᵣ
        speJumpTable.take i) ∗
        ((((base + bv% (ls_xref%
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44))) +
          BitVec.ofNat 64 i) ↦₈ᵣ b) ∗
         (((base + bv% (ls_xref%
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44))) +
          BitVec.ofNat 64 i + 1#64) ↦ᵣ speJumpTable.drop (i + 1))) := by
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen]
  rw [h, BitVec.add_assoc base
    (bv% (ls_xref%
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44)))
    (BitVec.ofNat 64 i), hoff]
  exact SatEntails.trans (SatEntails.drop_left _ _) (SatEntails.drop_right _ _)

private theorem stackAt_dropSpeX_split (sp : BitVec 64) :
    stackAt sp dropSpeStackX =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

private theorem stack_restore_32_speX (sp fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    stackAt sp dropSpeStackX := by
  rw [stackAt_dropSpeX_split sp]
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))

private theorem spe_word8_40_entails_48 (a w : BitVec 64) :
    (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ⊢ memRegion a 48 := by
  rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split a 8 40 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a w)

private theorem spe_word_pre_weaken (a : BitVec 64) {ro_tbl ro_byte : SepProp}
    (i : Nat) (w : BitVec 64) (hw : speWord i = w)
    (hbyte : SatEntails ro_tbl ro_byte) (rest : SepProp) :
    SatEntails (ro_tbl ∗ ((a ↦₆₄ speWord i) ∗ rest))
      ((a ↦₆₄ w) ∗ ro_byte ∗ rest) := by
  subst hw
  refine SatEntails.trans (SatEntails.sepConj_mono_left hbyte) ?_
  exact SatEntails.of_eq (by ac_rfl)

private theorem spe_word_post_weaken (a w sp fp lr x20 x19 : BitVec 64) (ro pool : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ ro ∗ memRegion (a + 8#64) 40 ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (spe_word8_40_entails_48 a w)
  have hst := SatEntails.of_entails (stack_restore_32_speX sp fp lr x20 x19)
  have hreord :
      (a ↦₆₄ w) ∗ ro ∗ memRegion (a + 8#64) 40 ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40) ∗
        ((ro ∗ pool) ∗
          (stackAt (sp - 32#64) extHookStack ∗
            ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
            ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by ac_rfl
  rw [hreord]
  exact SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro hst)

private theorem cliSpeJumpTable_adrp_eq {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64)
    (he : entry = base + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")) :
    (entry + bv% (40) &&& bv% (2 ^ 64 - 4096)) =
      base + bv% (page% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)) := by
  subst he
  have hadd :
      base + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]") + bv% (40) =
        base + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40) := by
    rw [BitVec.add_assoc]; rfl
  rw [hadd, ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

theorem dropSpeWord_ok_main {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (dropSpeWordSpec A img) := by
  let _ := hA
  simp only [Spec.inImage, dropSpeWordSpec, pure_sepConj_pure_assoc]
  code_fetches CryptoVerification.libsignalSessionCode cliDropSpeWordBin img.base
    (Rust.withPanics ext)
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")
    (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")) 184
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hadp : (
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" +
        bv% (40)) &&&
      bv% (2 ^ 64 - 4096)) =
      img.base + bv% (page% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)) :=
    cliSpeJumpTable_adrp_eq hb
      (fnAddr_rebase_eq_add_of_fnOff
        (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]"))
  dsimp only [tripleRatchetProgAtExt, cliDropSpeName, BitVec.ofNat_eq_ofNat] at ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" = fnBase
  examples_hide_fetches
  wp_init x s0
  obtain ⟨a, w⟩ := x
  dsimp only at *
  have ha : s0.readReg64 (Reg.gpr 0#5) = a := by assumption
  have hw : w = 13 ∨ w = 14 := by assumption
  subst ha
  have hro : img.RoDataLoaded s0.mem :=
    (Obj.Image.frozenLoaded_iff.mp ‹img.FrozenLoaded s0›).2.1
  refine SepWP.intro_rodata_cliSpeJumpTable himg hro ?_
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  rcases hw with rfl | rfl
  · refine SepWP.weaken_pre_sat
      (spe_word_pre_weaken (s0.readReg64 (Reg.gpr 0#5))
        13 0x800000000000000d#64 rfl
        (cliSpeJumpTable_byte img.base 13
          (bv% (ls_xref%
            (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
            (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 13))
          0x1b#8 rfl rfl rfl) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (spe_word_post_weaken _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  · refine SepWP.weaken_pre_sat
      (spe_word_pre_weaken (s0.readReg64 (Reg.gpr 0#5))
        14 0x800000000000000e#64 rfl
        (cliSpeJumpTable_byte img.base 14
          (bv% (ls_xref%
            (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
            (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 14))
          0x1b#8 rfl rfl rfl) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (spe_word_post_weaken _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done

end CryptoVerification.SignalSession.Cli.Store.DropSpeWord.Helpers
