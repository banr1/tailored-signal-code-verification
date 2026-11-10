/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common
import ProofLib.SepLogic.Entry

/-!
# `AllocContractsX` Verification of `drop_glue<SignalProtocolError>`

Proves the `extHookStack` contract `dropSpeSpecX` for
`core::ptr::drop_glue::<SignalProtocolError>` under `AllocContractsX`.
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


private theorem stackAt_dropSpeX_split (sp : BitVec 64) :
    stackAt sp dropSpeStackX =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  stackAt_split_cells sp extHookStack 4 (by decide)

private theorem tail_stack_32_from_bottomX (sp : BitVec 64) :
    memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 := by
  rw [show (16416#64 : BitVec 64) = BitVec.ofNat 64 (extHookStack + 32) from rfl,
      ← stackAt_split_bottom sp extHookStack 32 (by decide),
      show extHookStack + 32 = dropSpeStackX from rfl,
      ← stackAt_dropSpeX_split sp]

private theorem cells4_entails_stack_bottomX (sp : BitVec 64)
    (fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack := by
  rw [tail_stack_32_from_bottomX sp]
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))

private theorem stack_restore_32_speX (sp fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    stackAt sp dropSpeStackX := by
  rw [stackAt_dropSpeX_split sp, ← tail_stack_32_from_bottomX sp]
  exact cells4_entails_stack_bottomX sp fp lr x20 x19

private theorem spe_str_cap0_pre_weaken_fullX (a w cap ptr sp fp lr x20 x19 : BitVec 64) (ro pool : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) :=
  SatEntails.trans (spe_str_cap0_pre_weaken a w cap ptr ro pool _)
    (SatEntails.of_entails (sepConj_mono_right (sepConj_mono_right (stack_restore_32_speX sp fp lr x20 x19))))

private theorem spe_noop_pre_weaken_fullX (a w sp fp lr x20 x19 : BitVec 64) (ro pool : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) :=
  SatEntails.trans (spe_noop_pre_weaken a w ro pool _)
    (SatEntails.of_entails (sepConj_mono_right (sepConj_mono_right (stack_restore_32_speX sp fp lr x20 x19))))

private theorem spe_tail_dealloc_pre_weakenX (a w cap ptr sp : BitVec 64)
    (fp lr x20 x19 : BitVec 64) (ro live1 live2 pool : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ live1 ∗ live2 ∗ pool ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack ∗ (live1 ∗ live2)) := by
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
  refine SatEntails.trans (SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro (SatEntails.sepConj_mono_left hst))) ?_
  exact SatEntails.of_eq (by ac_rfl)

private theorem spe_tail_dealloc_postX (a : BitVec 64) (pool : SepProp) (sp : BitVec 64) :
    pool ∗ stackAt sp extHookStack ∗ memRegion a 48 ∗ memRegion (sp - 16416#64) 32 ⊢
      memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX := by
  rw [stackAt_dropSpeX_split sp, ← tail_stack_32_from_bottomX sp]
  exact Entails.of_eq (by ac_rfl)

private theorem vecU8_at_8_exposeX (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
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
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
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

private theorem speAt_invalidState_exposeX (A : RustAlloc) (fnName : List (BitVec 8))
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
    (SatEntails.sepConj_mono_right (SatEntails.sepConj_mono_right (strRefAt_entails_memRegion16 (a + 32#64) fnName))) ?_
  apply SatEntails.of_entails
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_exposeX A a bs)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

private theorem speAt_invalidMessage_exposeX (A : RustAlloc) (fnName : List (BitVec 8))
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
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_exposeX A a bs)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

private theorem spe_str_pre_weakenX (A : RustAlloc) (fnName : List (BitVec 8))
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
  exact SatEntails.of_eq (by ac_rfl)

private theorem SepWP.seq_callInv {prog : Program} {img : Obj.Image} {mid_pc target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid_pc s P (fun sm P_m =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWP prog target_pc sm P_m post)) :
    SepWP prog target_pc s P post := by
  unfold SepWP reaches_pc at h1 ⊢
  intro R hm hL
  obtain ⟨sm, hsteps1, ⟨_, _, P_m, hm_m, h2⟩ | ⟨hoom1, hfalse1⟩⟩ := h1 R hm hL
  · have hfrozen_m : img.FrozenLoaded sm := hfrozen.of_keepsFrozen hsteps1.keepsFrozen
    have hsym_m : sm.symtab = img.symtab := hsteps1.symtab_eq.trans hsym
    obtain ⟨sf, hsteps2, hout2⟩ := h2 hfrozen_m hsym_m R hm_m (hsteps1.codeLoaded hL)
    exact ⟨sf, Steps.trans hsteps1 hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr ⟨hoom1, hfalse1⟩⟩

theorem drop_spe_ok_x {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropSpeName)
      ((dropSpeSpecX A).inImage img) := by
  simp only [Spec.inImage, dropSpeSpecX, pure_sepConj_pure_assoc]
  have hdealloc := hA.dealloc_ok_at dropSpeName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]"))
    (by rw [(ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]")]; simp only [arm64_norm])
  simp only [Spec.inImage, rustDeallocExternSpecWithStack] at hdealloc
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
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  cases e with
  | panic =>
    simp only [speAt]
    exact SepWP.false_elim
  | invalidState =>
    refine SepWP.weaken_pre_sat
      (spe_str_pre_weakenX A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidState
        1 0x8000000000000001#64 rfl
        (speJumpTable_byte img.base 1 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 1)) 0x00#8 rfl rfl rfl)
        (speAt_invalidState_exposeX A fnName (s0.readReg64 (Reg.gpr 0#5))) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine SepWP.weaken_pre_sat (spe_str_cap0_pre_weaken_fullX _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hlay1, hlay2, hlay3⟩
      apply SepWP.seq_callInv (mid_pc := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]")) (by assumption) (by assumption)
      wp_steps
      refine SepWP.weaken_pre_sat
        (spe_tail_dealloc_pre_weakenX (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by rfl)
        (by simp only [State.status_setMem, State.status_setPC, State.status_writeReg64,
          State.status_setPState, hrun])
      intro hfrozen_call hsym_call
      wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done
  | invalidMessage t r =>
    refine SepWP.weaken_pre_sat
      (spe_str_pre_weakenX A fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidMessage t r)
        24 0x8000000000000018#64 rfl
        (speJumpTable_byte img.base 24 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 24)) 0x00#8 rfl rfl rfl)
        (speAt_invalidMessage_exposeX A fnName (s0.readReg64 (Reg.gpr 0#5)) t r) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine SepWP.weaken_pre_sat (spe_str_cap0_pre_weaken_fullX _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
      refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hlay1, hlay2, hlay3⟩
      apply SepWP.seq_callInv (mid_pc := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]")) (by assumption) (by assumption)
      wp_steps
      refine SepWP.weaken_pre_sat
        (spe_tail_dealloc_pre_weakenX (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _ _) ?_
      apply SepWP.done (by rfl)
        (by simp only [State.status_setMem, State.status_setPC, State.status_writeReg64,
          State.status_setPState, hrun])
      intro hfrozen_call hsym_call
      wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre (spe_tail_dealloc_postX (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done
  | invalidProtobufEncoding =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidProtobufEncoding
        2 0x8000000000000002#64 rfl
        (speJumpTable_byte img.base 2 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 2)) 0x1b#8 rfl rfl rfl) (SatEntails.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | ciphertextMessageTooShort n =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.ciphertextMessageTooShort n)
        3 0x8000000000000003#64 rfl
        (speJumpTable_byte img.base 3 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 3)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | legacyCiphertextVersion v =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.legacyCiphertextVersion v)
        4 0x8000000000000004#64 rfl
        (speJumpTable_byte img.base 4 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 4)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | unrecognizedCiphertextVersion v =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.unrecognizedCiphertextVersion v)
        5 0x8000000000000005#64 rfl
        (speJumpTable_byte img.base 5 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 5)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | noKeyTypeIdentifier =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .noKeyTypeIdentifier
        7 0x8000000000000007#64 rfl
        (speJumpTable_byte img.base 7 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 7)) 0x1b#8 rfl rfl rfl) (SatEntails.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | badKeyType t =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyType t)
        8 0x8000000000000008#64 rfl
        (speJumpTable_byte img.base 8 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 8)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | badKeyLength n =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyLength n)
        9 0x8000000000000009#64 rfl
        (speJumpTable_byte img.base 9 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 9)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | invalidKeyAgreement =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidKeyAgreement
        10 0x800000000000000a#64 rfl
        (speJumpTable_byte img.base 10 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 10)) 0x1b#8 rfl rfl rfl) (SatEntails.refl _) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | invalidSessionStructure r =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidSessionStructure r)
        20 0x8000000000000014#64 rfl
        (speJumpTable_byte img.base 20 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 20)) 0x1b#8 rfl rfl rfl)
        (by simp only [speAt]; exact SatEntails.sepConj_mono_right (spe_strRef_at_8_entails_40 _ _)) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | duplicatedMessage idx c =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.duplicatedMessage idx c)
        23 0x8000000000000017#64 rfl
        (speJumpTable_byte img.base 23 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44) + 23)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails (by simp only [speAt]; exact sepConj_mono_right (spe_u32x2_at_8_entails_40 _ _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (spe_noop_pre_weaken_fullX _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done

end CryptoVerification.LibsignalTripleRatchet.Getters
