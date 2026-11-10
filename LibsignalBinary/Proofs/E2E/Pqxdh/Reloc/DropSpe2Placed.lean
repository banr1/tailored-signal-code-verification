/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Ext
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.RelocCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common
import ProofLib.SepLogic.WP.Apply

/-!
# Relocatable `[LibsignalPlacement]` Contracts for `drop_glue::<SignalProtocolError> [local#2]` (Block `511`)

Proves `withLsRoLoaded lsmpl (dropSpeSpec A)` and `withLsRoLoaded lsmpl (dropSpe2VerSpec A)` on
Block `511` (`core::ptr::drop_glue::<SignalProtocolError> [local#2]`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.Getters

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open DropGlueFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

abbrev spe2JumpTableSym : String :=
  "libsignal_cli_handshake:.rodata.core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError>"

private theorem lsroCheck_spe2JumpTable : lsroCheck spe2JumpTableSym speJumpTable = true := by
  rfl_kernel

private theorem SepWP.intro_lsro_spe2JumpTable [LibsignalPlacement]
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWP prog target_pc s (((lsρ spe2JumpTableSym) ↦ᵣ speJumpTable) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  have hR := h R
  rw [sepConj_assoc] at hR
  exact hR (lsro_intro_chk hro lsroCheck_spe2JumpTable hm)

private theorem spe2JumpTable_placed_byte (base : BitVec 64) (i : Nat) (b : BitVec 8)
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

private theorem spe2_false_elim {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  have heq : (P ∗ ⌜False⌝ ∗ Q) ∗ R = ⌜False⌝ ∗ (P ∗ Q ∗ R) := by ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact False.elim hm.1

/-- Block `511` (`core::ptr::drop_glue::<SignalProtocolError> [local#2]`)
meets `withLsRoLoaded lsmpl (dropSpeSpec A)` under `[LibsignalPlacement]`, given `subroutine_ok`
for `__rust_dealloc`. -/
theorem drop_spe2_placed_ok_of_dealloc [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_511).rebase (blkPl_511).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_511).rebase (blkPl_511).base H) (blkPl_511).base
      (withLsRoLoaded lsmpl (dropSpeSpec A)) := by
  simp only [withLsRoLoaded, dropSpeSpec]
  simp only [rustDeallocSpec] at hdealloc
  wp_init x s0
  obtain ⟨a, fnName, e⟩ := x
  dsimp only at *
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = a := by assumption
  subst hx0
  have hro : LibsignalRoLoaded lsmpl s0.mem := by assumption
  refine SepWP.intro_lsro_spe2JumpTable hro ?_
  nth_rw 1 [stackAt_dropSpe_split s0.sp]
  cells_unfold
  wp_pull_exists
  cases e with
  | panic =>
    simp only [speAt]
    exact spe2_false_elim
  | invalidState =>
    refine SepWP.weaken_pre_sat
      (spe_str_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidState
        1 0x8000000000000001#64 rfl
        (spe2JumpTable_placed_byte (lsρ spe2JumpTableSym) 1 0x00#8 rfl rfl)
        (speAt_invalidState_expose A fnName (s0.readReg64 (Reg.gpr 0#5))) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, emp_sepConj]
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
        (spe2JumpTable_placed_byte (lsρ spe2JumpTableSym) 24 0x00#8 rfl rfl)
        (speAt_invalidMessage_expose A fnName (s0.readReg64 (Reg.gpr 0#5)) t r) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, emp_sepConj]
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
        (spe2JumpTable_placed_byte (lsρ spe2JumpTableSym) 2 0x1b#8 rfl rfl) (SatEntails.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | ciphertextMessageTooShort n =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.ciphertextMessageTooShort n)
        3 0x8000000000000003#64 rfl
        (spe2JumpTable_placed_byte (lsρ spe2JumpTableSym) 3 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | legacyCiphertextVersion v =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.legacyCiphertextVersion v)
        4 0x8000000000000004#64 rfl
        (spe2JumpTable_placed_byte (lsρ spe2JumpTableSym) 4 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | unrecognizedCiphertextVersion v =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.unrecognizedCiphertextVersion v)
        5 0x8000000000000005#64 rfl
        (spe2JumpTable_placed_byte (lsρ spe2JumpTableSym) 5 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | noKeyTypeIdentifier =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .noKeyTypeIdentifier
        7 0x8000000000000007#64 rfl
        (spe2JumpTable_placed_byte (lsρ spe2JumpTableSym) 7 0x1b#8 rfl rfl) (SatEntails.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | badKeyType t =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyType t)
        8 0x8000000000000008#64 rfl
        (spe2JumpTable_placed_byte (lsρ spe2JumpTableSym) 8 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | badKeyLength n =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyLength n)
        9 0x8000000000000009#64 rfl
        (spe2JumpTable_placed_byte (lsρ spe2JumpTableSym) 9 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | invalidKeyAgreement =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidKeyAgreement
        10 0x800000000000000a#64 rfl
        (spe2JumpTable_placed_byte (lsρ spe2JumpTableSym) 10 0x1b#8 rfl rfl) (SatEntails.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | invalidSessionStructure r =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidSessionStructure r)
        20 0x8000000000000014#64 rfl
        (spe2JumpTable_placed_byte (lsρ spe2JumpTableSym) 20 0x1b#8 rfl rfl)
        (by simp only [speAt]; exact SatEntails.sepConj_mono_right (spe_strRef_at_8_entails_40 _ _)) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | duplicatedMessage idx c =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.duplicatedMessage idx c)
        23 0x8000000000000017#64 rfl
        (spe2JumpTable_placed_byte (lsρ spe2JumpTableSym) 23 0x1b#8 rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u32x2_at_8_entails_40 _ _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done

/-- Block `511` (`core::ptr::drop_glue::<SignalProtocolError> [local#2]`)
meets `withLsRoLoaded lsmpl (dropSpeSpec A)` under `[LibsignalPlacement]`. -/
theorem drop_spe2_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_511).rebase (blkPl_511).base H) (blkPl_511).base
      (withLsRoLoaded lsmpl (dropSpeSpec A)) :=
  drop_spe2_placed_ok_of_dealloc (ls_hook_ok_rustDealloc h_dealloc)

theorem drop_spe2_placed_ok_at [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec A))) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeLoaded_of_plain (drop_spe2_placed_ok h_dealloc)) hi

theorem drop_spe2_placed_cl_ok_at [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 511)
      (withLsCl lsmpl (withLsRoLoaded lsmpl (dropSpeSpec A))) :=
  ls_subroutine_ok_cl_of_plain (callerProg := callerProg) (drop_spe2_placed_ok h_dealloc) hi

/-! ## `UnrecognizedMessageVersion` (Tag `6`) Variant (`dropSpe2VerSpec`) -/

/-- Spec for dropping `SignalProtocolError::UnrecognizedMessageVersion` (`0x8000000000000006#64`),
matching `ResponderClosure.P3P4.dropSpeVerSpec`. -/
def dropSpe2VerSpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 32) where
  pre := fun (a, msgVer) s =>
    ⌜s.readReg64 .x0 = a⌝ ∗
    (a ↦₆₄ 0x8000000000000006#64) ∗
    ((a + 8#64) ↦₃₂ msgVer) ∗
    memRegion (a + 12#64) 36 ∗
    A.pool ∗
    stackAt s.sp dropSpeStack
  post := fun (a, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    memRegion a 48 ∗
    A.pool ∗
    stackAt s0.sp dropSpeStack

private theorem spe_u32_at_8_entails_40 (a : BitVec 64) (v : BitVec 32) :
    ((a + 8#64) ↦₃₂ v) ∗ memRegion (a + 12#64) 36 ⊢ memRegion (a + 8#64) 40 := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 4 ∗ memRegion (a + 12#64) 36 := by
    rw [show (40 : Nat) = 4 + 36 from rfl, memRegion_split (a + 8#64) 4 36 (by decide),
        show a + 8#64 + 4#64 = a + 12#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left
    (IsBlock.entails (IsBlock.pointsTo32 (a + 8#64) v) (IsBlock.memRegion (a + 8#64) 4)
      fun _ _ => trivial)

private theorem spe_ver_pre_weaken {ro_tbl ro_byte : SepProp} (a : BitVec 64) (msgVer : BitVec 32)
    (hbyte : SatEntails ro_tbl ro_byte) (rest : SepProp) :
    SatEntails
      (ro_tbl ∗ ((a ↦₆₄ 0x8000000000000006#64) ∗ ((a + 8#64) ↦₃₂ msgVer) ∗
        memRegion (a + 12#64) 36 ∗ rest))
      ((a ↦₆₄ 0x8000000000000006#64) ∗ memRegion (a + 8#64) 40 ∗ ro_byte ∗ rest) := by
  have hu32 : SatEntails (((a + 8#64) ↦₃₂ msgVer) ∗ memRegion (a + 12#64) 36)
      (memRegion (a + 8#64) 40) :=
    SatEntails.of_entails (spe_u32_at_8_entails_40 a msgVer)
  have hreord :
      (a ↦₆₄ 0x8000000000000006#64) ∗ ((a + 8#64) ↦₃₂ msgVer) ∗
        memRegion (a + 12#64) 36 ∗ rest =
      (a ↦₆₄ 0x8000000000000006#64) ∗
        (((a + 8#64) ↦₃₂ msgVer) ∗ memRegion (a + 12#64) 36) ∗ rest := by ac_rfl
  rw [hreord]
  refine SatEntails.trans
    (SatEntails.sepConj_mono hbyte (SatEntails.sepConj_mono_right (SatEntails.sepConj_mono_left hu32))) ?_
  exact SatEntails.of_eq (by ac_rfl)

/-- Block `511` meets `withLsRoLoaded lsmpl (dropSpe2VerSpec A)` under `[LibsignalPlacement]`
(no deallocation hook required since tag `6` is a unit-like `u32` payload variant). -/
theorem drop_spe2_ver_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} :
    subroutine_ok ((blkPC_511).rebase (blkPl_511).base H) (blkPl_511).base
      (withLsRoLoaded lsmpl (dropSpe2VerSpec A)) := by
  simp only [withLsRoLoaded, dropSpe2VerSpec]
  wp_init x s0
  obtain ⟨a, msgVer⟩ := x
  dsimp only at *
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = a := by assumption
  subst hx0
  have hro : LibsignalRoLoaded lsmpl s0.mem := by assumption
  refine SepWP.intro_lsro_spe2JumpTable hro ?_
  nth_rw 1 [stackAt_dropSpe_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre_sat
    (spe_ver_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) msgVer
      (spe2JumpTable_placed_byte (lsρ spe2JumpTableSym) 6 0x1b#8 rfl rfl) _) ?_
  wp_steps
  refine SepWP.weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
  wp_done

theorem drop_spe2_ver_placed_ok_at [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpe2VerSpec A))) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeLoaded_of_plain drop_spe2_ver_placed_ok) hi

theorem drop_spe2_ver_placed_cl_ok_at [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 511)
      (withLsCl lsmpl (withLsRoLoaded lsmpl (dropSpe2VerSpec A))) :=
  ls_subroutine_ok_cl_of_plain (callerProg := callerProg) drop_spe2_ver_placed_ok hi

end CryptoVerification.LibsignalTripleRatchet.Getters
