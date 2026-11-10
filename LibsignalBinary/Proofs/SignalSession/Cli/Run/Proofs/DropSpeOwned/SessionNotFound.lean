/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwned.Common
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
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

private theorem strRefAt_entails_memRegion16 (a : BitVec 64) (lit : List (BitVec 8)) :
    SatEntails (strRefAt a lit) (memRegion a 16) := by
  unfold strRefAt
  apply SatEntails.sepExists_elim
  intro p
  refine SatEntails.trans (SatEntails.sepConj_mono_right (SatEntails.drop_right _ _)) ?_
  apply SatEntails.of_entails
  rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split a 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a p)
    (pointsTo64_entails_memRegion (a + 8#64) _)

private theorem snf_words_entails_48 (a cap ptr : BitVec 64) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ⊢ memRegion a 48 := by
  have h1 : memRegion a 48 = memRegion a 8 ∗ memRegion (a + 8#64) 40 := by
    rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split a 8 40 (by decide)]
  have h2 : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 := by
    rw [show (40 : Nat) = 8 + 32 from rfl, memRegion_split (a + 8#64) 8 32 (by decide),
        show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  have h3 := sepConj_mono (pointsTo64_entails_memRegion a cap)
    (sepConj_mono_left (pointsTo64_entails_memRegion (a + 8#64) ptr)
      (Q := memRegion (a + 16#64) 32))
  rw [h1, h2]
  exact h3

private theorem snf_cap0_pre_weaken_fullX (a cap ptr sp fp lr x20 x19 : BitVec 64)
    (ro pool : SepProp) :
    SatEntails
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ∗
        ro ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (snf_words_entails_48 a cap ptr)
  have hst := SatEntails.of_entails (stack_restore_32_speX sp fp lr x20 x19)
  have hreord :
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ∗
        ro ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32) ∗
        ((ro ∗ pool) ∗
          (stackAt (sp - 32#64) extHookStack ∗
            ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
            ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by ac_rfl
  rw [hreord]
  exact SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro hst)

private theorem snf_tail_dealloc_pre_weakenX (a cap ptr sp : BitVec 64)
    (fp lr x20 x19 : BitVec 64) (ro live1 live2 pool : SepProp) :
    SatEntails
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ∗
        ro ∗ live1 ∗ live2 ∗ pool ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack ∗
        (live1 ∗ live2)) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (snf_words_entails_48 a cap ptr)
  have hst := SatEntails.of_entails (cells4_entails_stack_bottomX sp fp lr x20 x19)
  have hreord :
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ∗
        ro ∗ live1 ∗ live2 ∗ pool ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) =
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32) ∗
        ((ro ∗ pool) ∗
         ((stackAt (sp - 32#64) extHookStack ∗
           ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
           ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ∗ (live1 ∗ live2))) := by ac_rfl
  rw [hreord]
  refine SatEntails.trans
    (SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro (SatEntails.sepConj_mono_left hst))) ?_
  exact SatEntails.of_eq (by ac_rfl)

private theorem vecU8_at_0_exposeX (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ∗ memRegion (a + 24#64) 24 ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1 ∧ cap.toNat < 2 ^ 63⌝ ∗
           A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have hexp : vecU8At A a cap ptr bs ⊢
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
      (if cap == 0#64 then emp
       else ⌜LayoutOk cap.toNat 1 ∧ cap.toNat < 2 ^ 63⌝ ∗
         A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
    refine Entails.trans (vecU8At_entails_dealloc A a cap ptr bs) ?_
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
      exact Entails.pure_right ⟨hlay, hcap_lt⟩ (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hexp) ?_
  have hm : memRegion (a + 16#64) 32 = memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 24 := by
    rw [show (32 : Nat) = 8 + 24 from rfl, memRegion_split (a + 16#64) 8 24 (by decide),
        show a + 16#64 + 8#64 = a + 24#64 by bv_omega]
  rw [hm]
  exact Entails.of_eq (by ac_rfl)

private theorem sessionNotFound_tail_entails_24 (a : BitVec 64) (dev : BitVec 8)
    (lit : List (BitVec 8)) :
    SatEntails
      (((a + 0x18#64) ↦₈ dev) ∗ memRegion (a + 0x19#64) 7 ∗ strRefAt (a + 0x20#64) lit)
      (memRegion (a + 24#64) 24) := by
  have hd : a + 0x18#64 = a + 24#64 := by bv_omega
  have hr : a + 0x19#64 = a + 25#64 := by bv_omega
  have hs : a + 0x20#64 = a + 32#64 := by bv_omega
  rw [hd, hr, hs]
  refine SatEntails.trans
    (SatEntails.sepConj_mono_right
      (SatEntails.sepConj_mono_right (strRefAt_entails_memRegion16 (a + 32#64) lit))) ?_
  apply SatEntails.of_entails
  have h1 : memRegion (a + 24#64) 24 = memRegion (a + 24#64) 1 ∗ memRegion (a + 25#64) 23 := by
    rw [show (24 : Nat) = 1 + 23 from rfl, memRegion_split (a + 24#64) 1 23 (by decide),
        show a + 24#64 + 1#64 = a + 25#64 by bv_omega]
  have h2 : memRegion (a + 25#64) 23 = memRegion (a + 25#64) 7 ∗ memRegion (a + 32#64) 16 := by
    rw [show (23 : Nat) = 7 + 16 from rfl, memRegion_split (a + 25#64) 7 16 (by decide),
        show a + 25#64 + 7#64 = a + 32#64 by bv_omega]
  rw [h1, h2]
  exact sepConj_mono_left
    (IsBlock.entails (IsBlock.pointsTo8 (a + 24#64) dev) (IsBlock.memRegion (a + 24#64) 1)
      fun _ _ => trivial)

private theorem speOwnedAt_sessionNotFound_exposeX (A : RustAlloc) (a : BitVec 64)
    (addr : AddrVal) (op : String) :
    SatEntails (speOwnedAt A a (.sessionNotFound addr op))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        memRegion (a + 16#64) 32 ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1 ∧ cap.toNat < 2 ^ 63⌝ ∗
           A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  simp only [speOwnedAt, apiErrAt, addrCloneAt]
  have hreord :
      (vecU8 A a addr.name ∗ ((a + 0x18#64) ↦₈ addr.device) ∗ memRegion (a + 0x19#64) 7) ∗
        strRefAt (a + 0x20#64) (CryptoVerification.LibsignalTripleRatchetRepr.utf8 op) =
      vecU8 A a addr.name ∗
        (((a + 0x18#64) ↦₈ addr.device) ∗ memRegion (a + 0x19#64) 7 ∗
          strRefAt (a + 0x20#64) (CryptoVerification.LibsignalTripleRatchetRepr.utf8 op)) := by
    ac_rfl
  rw [hreord]
  refine SatEntails.trans
    (SatEntails.sepConj_mono_right
      (sessionNotFound_tail_entails_24 a addr.device
        (CryptoVerification.LibsignalTripleRatchetRepr.utf8 op))) ?_
  exact SatEntails.of_entails (vecU8_at_0_exposeX A a addr.name)

private theorem speOwned_snf_pre_weakenX (A : RustAlloc)
    (a : BitVec 64) {ro_tbl ro_byte : SepProp} (addr : AddrVal) (op : String)
    (hbyte : SatEntails ro_tbl ro_byte)
    (rest : SepProp) :
    SatEntails (ro_tbl ∗ (speOwnedAt A a (.sessionNotFound addr op) ∗ rest))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        memRegion (a + 16#64) 32 ∗ ro_byte ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1 ∧ cap.toNat < 2 ^ 63⌝ ∗
           A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ rest) := by
  refine SatEntails.trans
    (SatEntails.sepConj_mono hbyte
      (SatEntails.sepConj_mono_left (speOwnedAt_sessionNotFound_exposeX A a addr op))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails.sepExists_elim; intro cap
  apply SatEntails.sepExists_elim; intro ptr
  refine SatEntails.sepExists_right cap (SatEntails.sepExists_right ptr ?_)
  exact SatEntails.of_eq (by ac_rfl)

@[local simp, local arm64_norm, local wp_norm]
private theorem conditionHolds_hi_addsPState64 (x y : BitVec 64) :
    ConditionHolds .HI (addsPState64 x y) = (BitVec.ult (x + y) x && (x + y != 0#64)) := by
  have hcs := conditionHolds_cs_addsPState64 x y
  have hne := conditionHolds_ne_addsPState64 x y
  cases h : addsPState64 x y with
  | mk n z c v =>
    rw [h] at hcs hne
    dsimp [ConditionHolds] at hcs hne ⊢
    rw [hcs, hne]

private theorem snf_xor_ult_35_eq_false {cap : BitVec 64} (hcap_lt : cap.toNat < 2 ^ 63) :
    BitVec.ult (cap ^^^ 0x8000000000000000#64) 35#64 = false := by
  have hb1 : cap.getLsbD 63 = false := by
    simp only [BitVec.getLsbD]
    exact Nat.testBit_lt_two_pow hcap_lt
  have hb2 : (0x8000000000000000#64 : BitVec 64).getLsbD 63 = true := by decide
  have hbx : (cap ^^^ 0x8000000000000000#64).getLsbD 63 = true := by
    rw [BitVec.getLsbD_xor, hb1, hb2]
    rfl
  have hge : 2 ^ 63 ≤ (cap ^^^ 0x8000000000000000#64).toNat := by
    by_contra hlt
    have hf : (cap ^^^ 0x8000000000000000#64).getLsbD 63 = false := by
      simp only [BitVec.getLsbD]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_not_le hlt)
    rw [hbx] at hf
    exact Bool.noConfusion hf
  have h35 : (35#64 : BitVec 64).toNat = 35 := rfl
  simp only [BitVec.ult, h35]
  exact decide_eq_false (by omega)

private theorem snf_cmn3_ult_eq_false {cap : BitVec 64}
    (hcap : cap ≠ 0#64) (hcap_lt : cap.toNat < 2 ^ 63) :
    BitVec.ult ((cap - 1#64) + 3#64) (cap - 1#64) = false := by
  have hpos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun h0 => hcap (BitVec.eq_of_toNat_eq h0))
  simp only [BitVec.ult]
  exact decide_eq_false (by bv_omega)

private theorem snf_add2_ult_sub1_eq_false {cap : BitVec 64}
    (hcap : cap ≠ 0#64) (hcap_lt : cap.toNat < 2 ^ 63) :
    BitVec.ult (cap + 2#64) (cap - 1#64) = false := by
  have heq : cap + 2#64 = (cap - 1#64) + 3#64 := by bv_omega
  rw [heq]
  exact snf_cmn3_ult_eq_false hcap hcap_lt

set_option linter.unusedSimpArgs false in
theorem cliDropSpeOwned_snf_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeSnfSpecX A).inImage img) := by
  simp only [Spec.inImage, dropSpeSnfSpecX, pure_sepConj_pure_assoc]
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
  wp_init x s0
  obtain ⟨a, addr, op⟩ := x
  dsimp only at *
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = a := by assumption
  subst hx0
  have hfrozen : img.FrozenLoaded s0 := by assumption
  have hsym : s0.symtab = img.symtab := by assumption
  have hro : img.RoDataLoaded s0.mem := (Obj.Image.frozenLoaded_iff.mp hfrozen).2.1
  refine intro_rodata_speJumpTable himg hro ?_
  nth_rw 1 [stackAt_dropSpeX_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine weaken_pre_sat
    (speOwned_snf_pre_weakenX A (s0.readReg64 (Reg.gpr 0#5)) addr op
      (speJumpTable_byte img.base 19
        (bv% (ls_xref%
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 40)
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" + 44) + 19))
        0x13#8 rfl rfl rfl) _) ?_
  wp_pull_exists
  rename_i cap ptr
  by_cases hcap : cap = 0#64
  · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    wp_steps
    refine weaken_pre_sat (snf_cap0_pre_weaken_fullX _ _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
    refine SepWP.focus_pure (by sep_focus) ?_
    rintro ⟨⟨hlay1, hlay2, hlay3⟩, hcap_lt⟩
    have hlo_false : BitVec.ult (cap ^^^ 0x8000000000000000#64) 35#64 = false :=
      snf_xor_ult_35_eq_false hcap_lt
    have hhi_ult : BitVec.ult ((cap - 1#64) + 3#64) (cap - 1#64) = false :=
      snf_cmn3_ult_eq_false hcap hcap_lt
    have hhi_ult2 : BitVec.ult (cap + 2#64) (cap - 1#64) = false :=
      snf_add2_ult_sub1_eq_false hcap hcap_lt
    apply seq_callInv
      (mid_pc := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]"))
      hfrozen hsym
    wp_steps
    refine weaken_pre_sat
      (snf_tail_dealloc_pre_weakenX (s0.readReg64 (Reg.gpr 0#5)) cap ptr s0.sp
        _ _ _ _ _ _ _ _) ?_
    apply SepWP.done (by rfl)
      (by simp only [State.status_setMem, State.status_setPC, State.status_writeReg64,
        State.status_setPState, hrun])
    intro hfrozen_call hsym_call
    wp_call hdealloc (ptr, cap.toNat, 1)
    refine SepWP.weaken_pre (spe_tail_dealloc_postX (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
    wp_done

end

end CryptoVerification.SignalSession.Cli.RunProofs.DropSpeOwnedHelpers
