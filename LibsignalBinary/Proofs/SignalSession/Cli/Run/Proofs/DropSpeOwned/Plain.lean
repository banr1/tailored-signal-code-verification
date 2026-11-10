/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwned.Common
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.Entry

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.DropSpeOwnedHelpers

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunDrop

section

set_option maxRecDepth 200000
attribute [local irreducible] Program.fetch Program.externAt?

private theorem plain_tbl_weaken (base a : BitVec 64) (i : Nat) (w off : BitVec 64)
    (hw : speWord i = w)
    (hoff : bv% (ls_xref%
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44)) +
        BitVec.ofNat 64 i = off)
    (heq : speJumpTable = speJumpTable.take i ++ (0x1b#8 :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i)
    (rest : SepProp) :
    SatEntails
      (((base + bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44))) ↦ᵣ
          speJumpTable) ∗ ((a ↦₆₄ speWord i) ∗ memRegion (a + 8#64) 40 ∗ rest))
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ((base + off) ↦₈ᵣ 0x1b#8) ∗ rest) :=
  spe_plain_tbl_pre_weakenX a i w hw (speJumpTable_byte base i off 0x1b#8 hoff heq hlen) rest

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_plainTag_tbl1_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    {i : Nat} (hi : i ∈ [2, 3, 4, 5, 6, 7, 8, 9, 10]) (a : BitVec 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (SpecAt ((dropSpePlainSpecX A).inImage img) ⟨a, i⟩) := by
  refine subroutine_ok_of_pure_pre hi ?_
  simp only [Spec.inImage, SpecAt, dropSpePlainSpecX, pure_sepConj_pure_assoc]
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin
    img.base (Rust.withPanics ext)
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")
    (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")) 184
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hadp : (
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" +
        bv% 40) &&&
      bv% (2 ^ 64 - 4096)) =
      img.base + bv% (page% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)) :=
    speJumpTable_adrp_eq hb
      (fnAddr_rebase_eq_add_of_fnOff
        (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]"))
  dsimp only [tripleRatchetProgAtExt, cliDropSpeName, BitVec.ofNat_eq_ofNat]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" = entry
  examples_hide_fetches
  wp_init u s0
  subst h
  have hro : img.RoDataLoaded s0.mem := (Obj.Image.frozenLoaded_iff.mp h_3).2.1
  refine intro_rodata_speJumpTable himg hro ?_
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_1
  rcases h_1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 2 0x8000000000000002#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 2))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 3 0x8000000000000003#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 3))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 4 0x8000000000000004#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 4))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 5 0x8000000000000005#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 5))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 6 0x8000000000000006#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 6))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 7 0x8000000000000007#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 7))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 8 0x8000000000000008#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 8))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 9 0x8000000000000009#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 9))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 10 0x800000000000000a#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 10))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_plainTag_tbl2_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    {i : Nat} (hi : i ∈ [11, 13, 14, 15, 16, 17, 20, 21, 23]) (a : BitVec 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (SpecAt ((dropSpePlainSpecX A).inImage img) ⟨a, i⟩) := by
  refine subroutine_ok_of_pure_pre hi ?_
  simp only [Spec.inImage, SpecAt, dropSpePlainSpecX, pure_sepConj_pure_assoc]
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin
    img.base (Rust.withPanics ext)
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")
    (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")) 184
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hadp : (
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" +
        bv% 40) &&&
      bv% (2 ^ 64 - 4096)) =
      img.base + bv% (page% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)) :=
    speJumpTable_adrp_eq hb
      (fnAddr_rebase_eq_add_of_fnOff
        (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]"))
  dsimp only [tripleRatchetProgAtExt, cliDropSpeName, BitVec.ofNat_eq_ofNat]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" = entry
  examples_hide_fetches
  wp_init u s0
  subst h
  have hro : img.RoDataLoaded s0.mem := (Obj.Image.frozenLoaded_iff.mp h_3).2.1
  refine intro_rodata_speJumpTable himg hro ?_
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_1
  rcases h_1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 11 0x800000000000000b#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 11))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 13 0x800000000000000d#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 13))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 14 0x800000000000000e#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 14))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 15 0x800000000000000f#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 15))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 16 0x8000000000000010#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 16))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 17 0x8000000000000011#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 17))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 20 0x8000000000000014#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 20))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 21 0x8000000000000015#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 21))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
  · refine weaken_pre_sat (plain_tbl_weaken img.base _ 23 0x8000000000000017#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 23))
      rfl rfl rfl rfl _) ?_
    wp_steps; refine weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_; wp_done

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_plainTag_hi_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (_himg : Obj.Loads libsignalSessionImage img)
    {i : Nat} (hi : i ∈ [28, 29, 30, 31, 32, 33, 34]) (a : BitVec 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (SpecAt ((dropSpePlainSpecX A).inImage img) ⟨a, i⟩) := by
  refine subroutine_ok_of_pure_pre hi ?_
  simp only [Spec.inImage, SpecAt, dropSpePlainSpecX, pure_sepConj_pure_assoc]
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin
    img.base (Rust.withPanics ext)
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")
    (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")) 184
  dsimp only [tripleRatchetProgAtExt, cliDropSpeName, BitVec.ofNat_eq_ofNat]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" = entry
  examples_hide_fetches
  wp_init u s0
  subst h
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_1
  rcases h_1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [show speWord 28 = 0x800000000000001c#64 from rfl]
    wp_steps; refine SepWP.weaken_pre (spe_kem_pre_weaken_fullX _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 29 = 0x800000000000001d#64 from rfl]
    wp_steps; refine SepWP.weaken_pre (spe_kem_pre_weaken_fullX _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 30 = 0x800000000000001e#64 from rfl]
    wp_steps; refine SepWP.weaken_pre (spe_kem_pre_weaken_fullX _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 31 = 0x800000000000001f#64 from rfl]
    wp_steps; refine SepWP.weaken_pre (spe_kem_pre_weaken_fullX _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 32 = 0x8000000000000020#64 from rfl]
    wp_steps; refine SepWP.weaken_pre (spe_kem_pre_weaken_fullX _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 33 = 0x8000000000000021#64 from rfl]
    wp_steps; refine SepWP.weaken_pre (spe_kem_pre_weaken_fullX _ _ s0.sp _ _ _ _ _) ?_; wp_done
  · simp only [show speWord 34 = 0x8000000000000022#64 from rfl]
    wp_steps; refine SepWP.weaken_pre (spe_kem_pre_weaken_fullX _ _ s0.sp _ _ _ _ _) ?_; wp_done

theorem cliDropSpeOwned_plain_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    {i : Nat} (hi : PlainSpeTag i) (a : BitVec 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (SpecAt ((dropSpePlainSpecX A).inImage img) ⟨a, i⟩) := by
  have hsplit :
      i ∈ [2, 3, 4, 5, 6, 7, 8, 9, 10] ∨
      i ∈ [11, 13, 14, 15, 16, 17, 20, 21, 23] ∨
      i ∈ [28, 29, 30, 31, 32, 33, 34] := by
    simp only [PlainSpeTag, plainSpeTags, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega
  rcases hsplit with h1 | h2 | h3
  · exact cliDropSpeOwned_plainTag_tbl1_ok_x himg h1 a
  · exact cliDropSpeOwned_plainTag_tbl2_ok_x himg h2 a
  · exact cliDropSpeOwned_plainTag_hi_ok_x himg h3 a

end

end CryptoVerification.SignalSession.Cli.RunProofs.DropSpeOwnedHelpers
