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
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
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

private def dropSpeWithStrRawSpecX (A : RustAlloc) : Spec (BitVec 64 × Nat) where
  pre := fun ⟨a, i⟩ s =>
    ⌜s.readReg64 .x0 = a⌝ ∗
      ((a ↦₆₄ speWord i) ∗ (∃∗ bs : List (BitVec 8), vecU8 A (a + 8#64) bs) ∗
        memRegion (a + 32#64) 16) ∗
      A.pool ∗ stackAt s.sp dropSpeStackX
  post := fun ⟨a, _⟩ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion a 48 ∗ A.pool ∗ stackAt s0.sp dropSpeStackX

private theorem spe_str_cap0_pre_weaken_fullX (a w cap ptr sp fp lr x20 x19 : BitVec 64)
    (ro pool : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (spe_str_words_entails_48 a w cap ptr)
  have hst := SatEntails.of_entails (stack_restore_32_speX sp fp lr x20 x19)
  have hreord :
      (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24) ∗
        ((ro ∗ pool) ∗
          (stackAt (sp - 32#64) extHookStack ∗
            ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
            ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by ac_rfl
  rw [hreord]
  exact SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro hst)

private theorem spe_tail_dealloc_pre_weakenX (a w cap ptr sp : BitVec 64)
    (fp lr x20 x19 : BitVec 64) (ro live1 live2 pool : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ live1 ∗ live2 ∗ pool ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack ∗
        (live1 ∗ live2)) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (spe_str_words_entails_48 a w cap ptr)
  have hst := SatEntails.of_entails (cells4_entails_stack_bottomX sp fp lr x20 x19)
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
  refine SatEntails.trans
    (SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro (SatEntails.sepConj_mono_left hst))) ?_
  exact SatEntails.of_eq (by ac_rfl)

private theorem str_tbl_weaken (A : RustAlloc) (base a : BitVec 64) (i : Nat)
    (w off : BitVec 64) (bs : List (BitVec 8))
    (hw : speWord i = w)
    (hoff : bv% (ls_xref%
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44)) +
        BitVec.ofNat 64 i = off)
    (heq : speJumpTable = speJumpTable.take i ++ (0x00#8 :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i)
    (rest : SepProp) :
    SatEntails
      (((base + bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44))) ↦ᵣ
          speJumpTable) ∗
        ((a ↦₆₄ speWord i) ∗ vecU8 A (a + 8#64) bs ∗ memRegion (a + 32#64) 16 ∗ rest))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ w) ∗
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ((base + off) ↦₈ᵣ 0x00#8) ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ rest) := by
  subst hw
  have hbyte := speJumpTable_byte base i off 0x00#8 hoff heq hlen
  have grouped :
      (a ↦₆₄ speWord i) ∗ vecU8 A (a + 8#64) bs ∗ memRegion (a + 32#64) 16 ∗ rest =
      (a ↦₆₄ speWord i) ∗ (vecU8 A (a + 8#64) bs ∗ memRegion (a + 32#64) 16) ∗ rest := by
    ac_rfl
  rw [grouped]
  refine SatEntails.trans
    (SatEntails.sepConj_mono hbyte
      (SatEntails.sepConj_mono_right
        (SatEntails.sepConj_mono_left (SatEntails.of_entails (vecU8_at_8_exposeX A a bs))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails.sepExists_elim; intro cap
  apply SatEntails.sepExists_elim; intro ptr
  refine SatEntails.sepExists_right cap (SatEntails.sepExists_right ptr ?_)
  exact SatEntails.of_eq (by ac_rfl)

theorem untrustedIdentity_entails_withString12 (A : RustAlloc) (a : BitVec 64)
    (addr : AddrVal) :
    speOwnedAt A a (.untrustedIdentity addr) ⊢
      speOwnedAt A a (.withString 12 (by decide)) := by
  simp only [speOwnedAt, apiErrAt, addrCloneAt, speUntrustedIdentity]
  have hd : (a + 8#64) + 0x18#64 = a + 32#64 := by bv_omega
  have hr : (a + 8#64) + 0x19#64 = a + 33#64 := by bv_omega
  have h1 : memRegion (a + 32#64) 16 = memRegion (a + 32#64) 1 ∗ memRegion (a + 33#64) 15 := by
    rw [show (16 : Nat) = 1 + 15 from rfl, memRegion_split (a + 32#64) 1 15 (by decide),
        show a + 32#64 + 1#64 = a + 33#64 by bv_omega]
  have h2 : memRegion (a + 33#64) 15 = memRegion (a + 33#64) 7 ∗ memRegion (a + 0x28#64) 8 := by
    rw [show (15 : Nat) = 7 + 8 from rfl, memRegion_split (a + 33#64) 7 8 (by decide),
        show a + 33#64 + 7#64 = a + 0x28#64 by bv_omega]
  have htail :
      (((a + 8#64) + 0x18#64) ↦₈ addr.device) ∗ memRegion ((a + 8#64) + 0x19#64) 7 ∗
        memRegion (a + 0x28#64) 8 ⊢ memRegion (a + 32#64) 16 := by
    rw [hd, hr, h1, h2]
    exact sepConj_mono_left
      (IsBlock.entails (IsBlock.pointsTo8 (a + 32#64) addr.device)
        (IsBlock.memRegion (a + 32#64) 1) fun _ _ => trivial)
  have hreord :
      (a ↦₆₄ speWord 12) ∗
        (vecU8 A (a + 8#64) addr.name ∗
          (((a + 8#64) + 0x18#64) ↦₈ addr.device) ∗ memRegion ((a + 8#64) + 0x19#64) 7) ∗
        memRegion (a + 0x28#64) 8 =
      (a ↦₆₄ speWord 12) ∗
        vecU8 A (a + 8#64) addr.name ∗
        ((((a + 8#64) + 0x18#64) ↦₈ addr.device) ∗ memRegion ((a + 8#64) + 0x19#64) 7 ∗
          memRegion (a + 0x28#64) 8) := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right
    (sepConj_mono (Entails.sepExists_right addr.name (Entails.refl _)) htail)

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_withStr1_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext)
    {i : Nat} (h4 : i ∈ [0, 1, 12, 18]) (a : BitVec 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (SpecAt ((dropSpeWithStrRawSpecX A).inImage img) ⟨a, i⟩) := by
  refine subroutine_ok_of_pure_pre h4 ?_
  simp only [Spec.inImage, SpecAt, dropSpeWithStrRawSpecX, pure_sepConj_pure_assoc]
  have hdealloc := hA.dealloc_ok_at cliDropSpeName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]"))
    (by
      rw [(ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")]
      simp only [arm64_norm])
  simp only [Spec.inImage, rustDeallocExternSpecWithStack] at hdealloc
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
  dsimp only [tripleRatchetProgAtExt, cliDropSpeName, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
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
  rcases h_1 with rfl | rfl | rfl | rfl
  · refine weaken_pre_sat (str_tbl_weaken A img.base _ 0 0x8000000000000000#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 0))
      v_stk rfl rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply seq_callInv (mid_pc := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")) h_3 h_2
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by rfl) (by simp only [State.status_setMem, State.status_setPC,
        State.status_writeReg64, State.status_setPState, hrun])
      intro _ _; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done
  · refine weaken_pre_sat (str_tbl_weaken A img.base _ 1 0x8000000000000001#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 1))
      v_stk rfl rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply seq_callInv (mid_pc := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")) h_3 h_2
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by rfl) (by simp only [State.status_setMem, State.status_setPC,
        State.status_writeReg64, State.status_setPState, hrun])
      intro _ _; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done
  · refine weaken_pre_sat (str_tbl_weaken A img.base _ 12 0x800000000000000c#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 12))
      v_stk rfl rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply seq_callInv (mid_pc := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")) h_3 h_2
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by rfl) (by simp only [State.status_setMem, State.status_setPC,
        State.status_writeReg64, State.status_setPState, hrun])
      intro _ _; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done
  · refine weaken_pre_sat (str_tbl_weaken A img.base _ 18 0x8000000000000012#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 18))
      v_stk rfl rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply seq_callInv (mid_pc := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")) h_3 h_2
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by rfl) (by simp only [State.status_setMem, State.status_setPC,
        State.status_writeReg64, State.status_setPState, hrun])
      intro _ _; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done

set_option linter.unusedSimpArgs false in
private theorem cliDropSpeOwned_withStr2_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext)
    {i : Nat} (h4 : i ∈ [22, 24, 25, 27]) (a : BitVec 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (SpecAt ((dropSpeWithStrRawSpecX A).inImage img) ⟨a, i⟩) := by
  refine subroutine_ok_of_pure_pre h4 ?_
  simp only [Spec.inImage, SpecAt, dropSpeWithStrRawSpecX, pure_sepConj_pure_assoc]
  have hdealloc := hA.dealloc_ok_at cliDropSpeName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]"))
    (by
      rw [(ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")]
      simp only [arm64_norm])
  simp only [Spec.inImage, rustDeallocExternSpecWithStack] at hdealloc
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
  dsimp only [tripleRatchetProgAtExt, cliDropSpeName, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
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
  rcases h_1 with rfl | rfl | rfl | rfl
  · refine weaken_pre_sat (str_tbl_weaken A img.base _ 22 0x8000000000000016#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 22))
      v_stk rfl rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply seq_callInv (mid_pc := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")) h_3 h_2
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by rfl) (by simp only [State.status_setMem, State.status_setPC,
        State.status_writeReg64, State.status_setPState, hrun])
      intro _ _; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done
  · refine weaken_pre_sat (str_tbl_weaken A img.base _ 24 0x8000000000000018#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 24))
      v_stk rfl rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply seq_callInv (mid_pc := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")) h_3 h_2
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by rfl) (by simp only [State.status_setMem, State.status_setPC,
        State.status_writeReg64, State.status_setPState, hrun])
      intro _ _; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done
  · refine weaken_pre_sat (str_tbl_weaken A img.base _ 25 0x8000000000000019#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 25))
      v_stk rfl rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply seq_callInv (mid_pc := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")) h_3 h_2
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by rfl) (by simp only [State.status_setMem, State.status_setPC,
        State.status_writeReg64, State.status_setPState, hrun])
      intro _ _; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done
  · refine weaken_pre_sat (str_tbl_weaken A img.base _ 27 0x800000000000001b#64
      (bv% (ls_xref%
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 27))
      v_stk rfl rfl rfl rfl _) ?_
    wp_pull_exists; rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps; refine weaken_pre_sat (spe_str_cap0_pre_weaken_fullX _ _ _ _ s0.sp _ _ _ _ _ _) ?_; wp_done
    · simp only [beq_eq_false_iff_ne.mpr hcap, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hlay1, hlay2, hlay3⟩
      apply seq_callInv (mid_pc := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]")) h_3 h_2
      wp_steps
      refine weaken_pre_sat (spe_tail_dealloc_pre_weakenX _ _ cap ptr s0.sp _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by rfl) (by simp only [State.status_setMem, State.status_setPC,
        State.status_writeReg64, State.status_setPState, hrun])
      intro _ _; wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX _ A.pool s0.sp) ?_; wp_done

theorem cliDropSpeOwned_withStr_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeWithStrSpecX A).inImage img) := by
  refine subroutine_ok_pointwise fun ⟨a, ⟨i, hi⟩⟩ => ?_
  change subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
    (SpecAt ((dropSpeWithStrRawSpecX A).inImage img) ⟨a, i⟩)
  have hsplit : i ∈ [0, 1, 12, 18] ∨ i ∈ [22, 24, 25, 27] := by
    simp only [StrSpeTag, strSpeTags, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega
  rcases hsplit with h1 | h2
  · exact cliDropSpeOwned_withStr1_ok_x himg hA h1 a
  · exact cliDropSpeOwned_withStr2_ok_x himg hA h2 a

end

end CryptoVerification.SignalSession.Cli.RunProofs.DropSpeOwnedHelpers
