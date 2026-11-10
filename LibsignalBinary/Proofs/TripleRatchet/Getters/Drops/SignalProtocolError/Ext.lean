/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessage
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common
import ProofLib.SepLogic.Entry
import ProofLib.SepLogic.WP.Apply

/-!
# Verification of `drop_glue<SignalProtocolError>`

Proves `dropSpeSpec` for `core::ptr::drop_glue::<SignalProtocolError>` on
`tripleRatchetProgAt` and under `[LibsignalPlacement]`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Getters

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open DropGlueFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?


private theorem SepWP.false_elim {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  have heq : (P ∗ ⌜False⌝ ∗ Q) ∗ R = ⌜False⌝ ∗ (P ∗ Q ∗ R) := by ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact False.elim hm.1


theorem drop_spe_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContracts img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropSpeName)
      ((dropSpeSpec A).inImage img) := by
  simp only [Spec.inImage, dropSpeSpec, pure_sepConj_pure_assoc]
  have hdealloc := hA.dealloc_ok_at dropSpeName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]"))
    (by rw [(ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]")]; simp only [arm64_norm])
  simp only [rustDeallocSpec] at hdealloc
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]")) 184
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hadp : (
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" +
        40#64) &&&
      bv% (2 ^ 64 - 4096)) = img.base + 8192#64 :=
    speJumpTable_adrp_eq hb (fnAddr_rebase_eq_add_of_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]"))
  dsimp only [tripleRatchetProgAtExt, dropSpeName, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨a, fnName, e⟩ := x
  dsimp only at *
  subst h
  have hro : img.RoDataLoaded s0.mem := (Obj.Image.frozenLoaded_iff.mp h_2).2.1
  refine SepWP.intro_rodata_speJumpTable himg hro ?_
  nth_rw 1 [stackAt_dropSpe_split s0.sp]
  cells_unfold
  wp_pull_exists
  cases e with
  | panic =>
    simp only [speAt]
    exact SepWP.false_elim
  | invalidState =>
    refine SepWP.weaken_pre_sat
      (spe_str_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidState
        1 0x8000000000000001#64 rfl
        (speJumpTable_byte img.base 1 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 1)) 0x00#8 rfl rfl rfl)
        (speAt_invalidState_expose A fnName (s0.readReg64 (Reg.gpr 0#5))) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine SepWP.weaken_pre_sat (DropGlueFacts.spe_str_cap0_pre_weaken_full _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
      wp_steps
      refine SepWP.weaken_pre_sat
        (spe_tail_dealloc_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _) ?_
      wp_apply
      refine SepWP.weaken_pre (DropGlueFacts.spe_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done
  | invalidMessage t r =>
    refine SepWP.weaken_pre_sat
      (spe_str_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidMessage t r)
        24 0x8000000000000018#64 rfl
        (speJumpTable_byte img.base 24 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 24)) 0x00#8 rfl rfl rfl)
        (speAt_invalidMessage_expose A fnName (s0.readReg64 (Reg.gpr 0#5)) t r) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine SepWP.weaken_pre_sat (DropGlueFacts.spe_str_cap0_pre_weaken_full _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
      wp_steps
      refine SepWP.weaken_pre_sat
        (spe_tail_dealloc_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _) ?_
      wp_apply
      refine SepWP.weaken_pre (DropGlueFacts.spe_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done
  | invalidProtobufEncoding =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidProtobufEncoding
        2 0x8000000000000002#64 rfl
        (speJumpTable_byte img.base 2 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 2)) 0x1b#8 rfl rfl rfl) (SatEntails.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | ciphertextMessageTooShort n =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.ciphertextMessageTooShort n)
        3 0x8000000000000003#64 rfl
        (speJumpTable_byte img.base 3 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 3)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | legacyCiphertextVersion v =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.legacyCiphertextVersion v)
        4 0x8000000000000004#64 rfl
        (speJumpTable_byte img.base 4 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 4)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | unrecognizedCiphertextVersion v =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.unrecognizedCiphertextVersion v)
        5 0x8000000000000005#64 rfl
        (speJumpTable_byte img.base 5 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 5)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | noKeyTypeIdentifier =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .noKeyTypeIdentifier
        7 0x8000000000000007#64 rfl
        (speJumpTable_byte img.base 7 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 7)) 0x1b#8 rfl rfl rfl) (SatEntails.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | badKeyType t =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyType t)
        8 0x8000000000000008#64 rfl
        (speJumpTable_byte img.base 8 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 8)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | badKeyLength n =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyLength n)
        9 0x8000000000000009#64 rfl
        (speJumpTable_byte img.base 9 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 9)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | invalidKeyAgreement =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidKeyAgreement
        10 0x800000000000000a#64 rfl
        (speJumpTable_byte img.base 10 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 10)) 0x1b#8 rfl rfl rfl) (SatEntails.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | invalidSessionStructure r =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidSessionStructure r)
        20 0x8000000000000014#64 rfl
        (speJumpTable_byte img.base 20 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 20)) 0x1b#8 rfl rfl rfl)
        (by simp only [speAt]; exact SatEntails.sepConj_mono_right (spe_strRef_at_8_entails_40 _ _)) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | duplicatedMessage idx c =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.duplicatedMessage idx c)
        23 0x8000000000000017#64 rfl
        (speJumpTable_byte img.base 23 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 23)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u32x2_at_8_entails_40 _ _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done

theorem drop_spe_ok_trap {A : RustAlloc} {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr dropSpeName)
      ((dropSpeSpec A).inImage img) :=
  drop_spe_ok_ext himg (AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs hA)

theorem drop_spe_ok {A : RustAlloc} {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr dropSpeName)
      ((dropSpeSpec A).inImage img) :=
  subroutine_ok_kit_of_trTrap (drop_spe_ok_trap himg hA)

/-! ## Relocatable `[LibsignalPlacement]` Contract -/

open Arm64.Obj CryptoVerification

abbrev speJumpTableSym : String :=
  "libsignal_protocol:.rodata.core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError>"

private theorem lsroCheck_speJumpTable : lsroCheck speJumpTableSym speJumpTable = true := by
  rfl_kernel

private theorem SepWP.intro_lsro_speJumpTable [LibsignalPlacement]
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWP prog target_pc s (((lsρ speJumpTableSym) ↦ᵣ speJumpTable) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  have hR := h R
  rw [sepConj_assoc] at hR
  exact hR (lsro_intro_chk hro lsroCheck_speJumpTable hm)

private theorem speJumpTable_placed_byte (base : BitVec 64) (i : Nat) (b : BitVec 8)
    (heq : speJumpTable = speJumpTable.take i ++ (b :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i) :
    SatEntails (base ↦ᵣ speJumpTable) ((base + BitVec.ofNat 64 i) ↦₈ᵣ b) := by
  have h : (base ↦ᵣ speJumpTable) =
      (base ↦ᵣ speJumpTable.take i) ∗
        (((base + BitVec.ofNat 64 i) ↦₈ᵣ b) ∗
         ((base + BitVec.ofNat 64 i + 1#64) ↦ᵣ speJumpTable.drop (i + 1))) := by
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen]
  rw [h]
  exact SatEntails.trans (SatEntails.drop_left _ _) (SatEntails.drop_right _ _)

/-- Add `⌜LibsignalRoLoaded pl s0.mem⌝` to `spec`'s precondition. -/
abbrev withLsRoLoaded {α : Type} (pl : MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜LibsignalRoLoaded pl s0.mem⌝ }

theorem drop_spe_placed_ok_of_dealloc [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_5).rebase (blkPl_5).base H) (blkPl_5).base
      (withLsRoLoaded lsmpl (dropSpeSpec A)) := by
  simp only [withLsRoLoaded, dropSpeSpec, pure_sepConj_pure_assoc]
  simp only [rustDeallocSpec] at hdealloc
  wp_init x s0
  obtain ⟨a, fnName, e⟩ := x
  dsimp only at *
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = a := by assumption
  subst hx0
  have hro : LibsignalRoLoaded lsmpl s0.mem := by assumption
  refine SepWP.intro_lsro_speJumpTable hro ?_
  nth_rw 1 [stackAt_dropSpe_split s0.sp]
  cells_unfold
  wp_pull_exists
  cases e with
  | panic =>
    simp only [speAt]
    exact SepWP.false_elim
  | invalidState =>
    refine SepWP.weaken_pre_sat
      (spe_str_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidState
        1 0x8000000000000001#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 1 0x00#8 rfl rfl)
        (speAt_invalidState_expose A fnName (s0.readReg64 (Reg.gpr 0#5))) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine SepWP.weaken_pre_sat (DropGlueFacts.spe_str_cap0_pre_weaken_full _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
      wp_steps
      refine SepWP.weaken_pre_sat
        (spe_tail_dealloc_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _) ?_
      wp_apply
      refine SepWP.weaken_pre (DropGlueFacts.spe_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done
  | invalidMessage t r =>
    refine SepWP.weaken_pre_sat
      (spe_str_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidMessage t r)
        24 0x8000000000000018#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 24 0x00#8 rfl rfl)
        (speAt_invalidMessage_expose A fnName (s0.readReg64 (Reg.gpr 0#5)) t r) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine SepWP.weaken_pre_sat (DropGlueFacts.spe_str_cap0_pre_weaken_full _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
      wp_steps
      refine SepWP.weaken_pre_sat
        (spe_tail_dealloc_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _) ?_
      wp_apply
      refine SepWP.weaken_pre (DropGlueFacts.spe_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done
  | invalidProtobufEncoding =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidProtobufEncoding
        2 0x8000000000000002#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 2 0x1b#8 rfl rfl) (SatEntails.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | ciphertextMessageTooShort n =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.ciphertextMessageTooShort n)
        3 0x8000000000000003#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 3 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | legacyCiphertextVersion v =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.legacyCiphertextVersion v)
        4 0x8000000000000004#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 4 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | unrecognizedCiphertextVersion v =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.unrecognizedCiphertextVersion v)
        5 0x8000000000000005#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 5 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | noKeyTypeIdentifier =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .noKeyTypeIdentifier
        7 0x8000000000000007#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 7 0x1b#8 rfl rfl) (SatEntails.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | badKeyType t =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyType t)
        8 0x8000000000000008#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 8 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | badKeyLength n =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyLength n)
        9 0x8000000000000009#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 9 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | invalidKeyAgreement =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidKeyAgreement
        10 0x800000000000000a#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 10 0x1b#8 rfl rfl) (SatEntails.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | invalidSessionStructure r =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidSessionStructure r)
        20 0x8000000000000014#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 20 0x1b#8 rfl rfl)
        (by simp only [speAt]; exact SatEntails.sepConj_mono_right (spe_strRef_at_8_entails_40 _ _)) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | duplicatedMessage idx c =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.duplicatedMessage idx c)
        23 0x8000000000000017#64 rfl
        (speJumpTable_placed_byte (lsρ speJumpTableSym) 23 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u32x2_at_8_entails_40 _ _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done

theorem drop_spe_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_5).rebase (blkPl_5).base H) (blkPl_5).base
      (withLsRoLoaded lsmpl (dropSpeSpec A)) :=
  drop_spe_placed_ok_of_dealloc (ls_hook_ok_rustDealloc h_dealloc)

end CryptoVerification.LibsignalTripleRatchet.Getters
