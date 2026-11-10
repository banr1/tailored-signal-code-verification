/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.ShardFill.DropGlueErrorSignalProtocolErrorL3
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common
import ProofLib.SepLogic.Entry
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2 -- shake: keep

/-!
# `drop_glue::<SignalProtocolError>` Proof on `tripleRatchetProgAt`

Verifies `core::ptr::drop_glue::<SignalProtocolError> [local#2]` (46 instructions) against
`(dropSpeSpec A).inImage img` on `trTrapProgAt` (`drop_spe2_ok_trap`) and `tripleRatchetProgAt`
(`drop_spe2_ok`).
-/

@[expose] public section

abbrev _root_.CryptoVerification.Cli.dropSpe2Name : String :=
  "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]"

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

/-! ## `.rodata` Jump Table & `drop_spe2_ok` Proofs -/

private theorem rodata_0x3f000_eq_cli_spe2 :
    (libsignalSessionImage.data.drop
      (num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44)) - num% (ls_xref% 0x2440 0x2444))).take 28 = speJumpTable := by
  rfl_kernel

private theorem rodata_speJumpTable_intro_cli_spe2 {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable) ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) (secLen := 28) (dataOff := num% (ls_xref% 0x2440 0x2444))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP
  rwa [rodata_0x3f000_eq_cli_spe2] at h

private theorem SepWP.intro_rodata_speJumpTable_cli_spe2 {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hro : img.RoDataLoaded s.mem)
    (h : SepWP prog target_pc s
      (((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  have hR := h R
  rw [sepConj_assoc] at hR
  exact hR (rodata_speJumpTable_intro_cli_spe2 himg hro hm)

private theorem speJumpTable_byte_cli_spe2 (base : BitVec 64) (i : Nat) (off : BitVec 64) (b : BitVec 8)
    (hoff : bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44)) + BitVec.ofNat 64 i = off)
    (heq : speJumpTable = speJumpTable.take i ++ (b :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i) :
    SatEntails ((base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable) ((base + off) ↦₈ᵣ b) := by
  have h : ((base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable) =
      ((base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable.take i) ∗
        ((((base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) + BitVec.ofNat 64 i) ↦₈ᵣ b) ∗
         (((base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) + BitVec.ofNat 64 i + 1#64) ↦ᵣ
           speJumpTable.drop (i + 1))) := by
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen]
  rw [h, BitVec.add_assoc base (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) (BitVec.ofNat 64 i), hoff]
  exact SatEntails.trans (SatEntails.drop_left _ _) (SatEntails.drop_right _ _)

private theorem SepWP.false_elim {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  have heq : (P ∗ ⌜False⌝ ∗ Q) ∗ R = ⌜False⌝ ∗ (P ∗ Q ∗ R) := by ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact False.elim hm.1

private theorem speJumpTable_adrp_eq_cli_spe2 {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64) (he : entry = base + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]"))) :
    (entry + 40#64 &&& 18446744073709547520#64) = base + (bv% (page% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40))) := by
  subst he
  have hadd : base + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")) + 40#64 = base + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40)) := by
    rw [BitVec.add_assoc]; rfl
  rw [hadd, adrp_page_of_aligned hb]
  rfl

/-- `core::ptr::drop_glue::<SignalProtocolError>` (`46 insns) meets
`(dropSpeSpec A).inImage img` on `trTrapProgAt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_spe2_ok_trap {A : RustAlloc} {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.dropSpe2Name)
      ((dropSpeSpec A).inImage img) := by
  simp only [Spec.inImage, dropSpeSpec, pure_sepConj_pure_assoc]
  have hdealloc_hs : HookSat (Rust.withPanics (trTrapExterns C abs)) "__rustc::__rust_dealloc"
      (rustDeallocSpec A) := by
    rcases DropGlueFacts.dealloc_hookSat_tripleRatchetExterns C 0#64 hA with ⟨fn, hfn, hok⟩
    exact ⟨fn, (withPanics_trTrap_ne C abs (by unfold rngFillName; decide)).trans hfn, hok⟩
  have hdealloc : subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr
        "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]"))))
      (rustDeallocSpec A) :=
    hook_ok_at_raw
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")
      (by decide) (by decide) (ls_hook% "__rustc::__rust_dealloc") hdealloc_hs
  simp only [rustDeallocSpec] at hdealloc
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli img.base
    (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]") (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]") 184
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hadp : (
      ((libsignalSessionCode.rebase img.base
        (Rust.withPanics (trTrapExterns C abs))).fnAddr
        "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" +
        40#64) &&&
      18446744073709547520#64) = img.base + (bv% (page% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40))) :=
    speJumpTable_adrp_eq_cli_spe2 hb (fnAddr_rebase_eq_add_of_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]"))
  dsimp only [trTrapProgAt, CryptoVerification.Cli.dropSpe2Name, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C abs))).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨a, fnName, e⟩ := x
  dsimp only at *
  subst h
  have hro : img.RoDataLoaded s0.mem := (Obj.Image.frozenLoaded_iff.mp h_2).2.1
  refine SepWP.intro_rodata_speJumpTable_cli_spe2 himg hro ?_
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
        (speJumpTable_byte_cli_spe2 img.base 1 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 1)) 0x00#8 rfl rfl rfl)
        (speAt_invalidState_expose A fnName (s0.readReg64 (Reg.gpr 0#5))) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine SepWP.weaken_pre_sat
        (DropGlueFacts.spe_str_cap0_pre_weaken_full _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
      wp_steps
      refine SepWP.weaken_pre_sat
        (spe_tail_dealloc_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _) ?_
      wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre
        (DropGlueFacts.spe_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done
  | invalidMessage t r =>
    refine SepWP.weaken_pre_sat
      (spe_str_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidMessage t r)
        24 0x8000000000000018#64 rfl
        (speJumpTable_byte_cli_spe2 img.base 24 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 24)) 0x00#8 rfl rfl rfl)
        (speAt_invalidMessage_expose A fnName (s0.readReg64 (Reg.gpr 0#5)) t r) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine SepWP.weaken_pre_sat
        (DropGlueFacts.spe_str_cap0_pre_weaken_full _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
      wp_steps
      refine SepWP.weaken_pre_sat
        (spe_tail_dealloc_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _) ?_
      wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre
        (DropGlueFacts.spe_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done
  | invalidProtobufEncoding =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidProtobufEncoding
        2 0x8000000000000002#64 rfl
        (speJumpTable_byte_cli_spe2 img.base 2 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 2)) 0x1b#8 rfl rfl rfl)
        (SatEntails.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | ciphertextMessageTooShort n =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.ciphertextMessageTooShort n)
        3 0x8000000000000003#64 rfl
        (speJumpTable_byte_cli_spe2 img.base 3 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 3)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | legacyCiphertextVersion v =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.legacyCiphertextVersion v)
        4 0x8000000000000004#64 rfl
        (speJumpTable_byte_cli_spe2 img.base 4 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 4)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | unrecognizedCiphertextVersion v =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.unrecognizedCiphertextVersion v)
        5 0x8000000000000005#64 rfl
        (speJumpTable_byte_cli_spe2 img.base 5 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 5)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | noKeyTypeIdentifier =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .noKeyTypeIdentifier
        7 0x8000000000000007#64 rfl
        (speJumpTable_byte_cli_spe2 img.base 7 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 7)) 0x1b#8 rfl rfl rfl)
        (SatEntails.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | badKeyType t =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyType t)
        8 0x8000000000000008#64 rfl
        (speJumpTable_byte_cli_spe2 img.base 8 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 8)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | badKeyLength n =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyLength n)
        9 0x8000000000000009#64 rfl
        (speJumpTable_byte_cli_spe2 img.base 9 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 9)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | invalidKeyAgreement =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidKeyAgreement
        10 0x800000000000000a#64 rfl
        (speJumpTable_byte_cli_spe2 img.base 10 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 10)) 0x1b#8 rfl rfl rfl)
        (SatEntails.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | invalidSessionStructure r =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidSessionStructure r)
        20 0x8000000000000014#64 rfl
        (speJumpTable_byte_cli_spe2 img.base 20 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 20)) 0x1b#8 rfl rfl rfl)
        (by simp only [speAt]
            exact SatEntails.sepConj_mono_right (spe_strRef_at_8_entails_40 _ _)) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | duplicatedMessage idx c =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.duplicatedMessage idx c)
        23 0x8000000000000017#64 rfl
        (speJumpTable_byte_cli_spe2 img.base 23 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 23)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u32x2_at_8_entails_40 _ _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done

/-- `core::ptr::drop_glue::<SignalProtocolError>` (`46 insns) meets
`(dropSpeSpec A).inImage img` on `tripleRatchetProgAt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_spe2_ok {A : RustAlloc} {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.dropSpe2Name)
      ((dropSpeSpec A).inImage img) :=
  trTrapProgAt_fnAddr_eq img.base C ctl abs CryptoVerification.Cli.dropSpe2Name ▸
    subroutine_ok_kit_of_trTrap (CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_spe2_ok_trap himg hA)

end CryptoVerification.LibsignalTripleRatchet.Getters
