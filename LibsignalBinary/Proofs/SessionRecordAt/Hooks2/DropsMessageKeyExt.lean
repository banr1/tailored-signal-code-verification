/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
public import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs -- shake: keep

@[expose] public section

set_option autoImplicit false

/-!
# `drop_glue::<Vec<MessageKey>>` (`0x1f28`)

Verifies `core::ptr::drop_glue::<Vec<session_structure::Chain::MessageKey>>` (`0x1f28`, Block `3`)
against `dropVecMessageKeySpecX A` at `dropVecMessageKeyStackX = extHookStack + 48` on `SP2Ext`
and under relocatable `[LibsignalPlacement]`.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_DropsMessageKeyExt : True := trivial

/-! ## Stack budget and specification -/

/-- Stack budget for `drop_glue::<Vec<MessageKey>>` (`extHookStack + 48`). -/
abbrev dropVecMessageKeyStackX : Nat := Stage1X.extHookStack + 48

/-- Specification of `drop_glue::<Vec<MessageKey>>` at `dropVecMessageKeyStackX`. -/
def dropVecMessageKeySpecX (A : RustAlloc) : Spec DropVecMessageKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v⌝ ∗
      vecAt A 104 8 (messageKeyAt A) x.v x.cap x.ptr x.mks ∗ A.pool ∗
      stackAt s.sp dropVecMessageKeyStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗ A.pool ∗ stackAt s0.sp dropVecMessageKeyStackX

/-! ## Stack splitting and restoration helpers -/

theorem stackAt_dropVecMessageKeyX_split (sp : BitVec 64) :
    stackAt sp dropVecMessageKeyStackX =
      stackAt (sp - 48#64) Stage1X.extHookStack ∗ cells (sp - 48#64) 6 := by
  exact ProofLib.stackAt_split_cells sp Stage1X.extHookStack 6 (by decide)

theorem stack_restore_48_extHook (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) Stage1X.extHookStack ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropVecMessageKeyStackX := by
  rw [stackAt_dropVecMessageKeyX_split sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

theorem tail_stack_48_from_bottom_ext (sp : BitVec 64) :
    memRegion (sp - 16432#64) 48 ∗ stackAt sp Stage1X.extHookStack =
      stackAt (sp - 48#64) Stage1X.extHookStack ∗ cells (sp - 48#64) 6 := by
  -- `extHookStack` is `2 ^ 14` (Mathlib `Monoid.npow`): `rw` cannot match `16432#64`; use defeq.
  have h : stackAt sp dropVecMessageKeyStackX =
      memRegion (sp - 16432#64) 48 ∗ stackAt sp Stage1X.extHookStack :=
    ProofLib.stackAt_split_bottom sp Stage1X.extHookStack 48 (by decide)
  rw [← h]
  exact stackAt_dropVecMessageKeyX_split sp

theorem cap0_weaken_48_extHook (v cap ptr : BitVec 64) (Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      Pool ∗ stackAt (sp - 48#64) Stage1X.extHookStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion v 24 ∗ Pool ∗ stackAt sp dropVecMessageKeyStackX := by
  refine Entails.trans (DropGlueFacts.header24_weaken v cap ptr _) ?_
  exact sepConj_mono_right (sepConj_mono_right (stack_restore_48_extHook sp fp lr x22 x21 x20 x19))

theorem tail_dealloc_pre_weaken_ext (v cap ptr : BitVec 64) (Live Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      Live ∗ Pool ∗
      stackAt (sp - 48#64) Stage1X.extHookStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion v 24 ∗ Live ∗ Pool ∗
      memRegion (sp - 16432#64) 48 ∗ stackAt sp Stage1X.extHookStack := by
  have h1 := header_cells_entails_memRegion_24 v cap ptr
  have h2 :
      stackAt (sp - 48#64) Stage1X.extHookStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
      memRegion (sp - 16432#64) 48 ∗ stackAt sp Stage1X.extHookStack := by
    rw [tail_stack_48_from_bottom_ext sp]
    exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)
  have hgroup :
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
        Live ∗ Pool ∗
        stackAt (sp - 48#64) Stage1X.extHookStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8) ∗
        Live ∗ Pool ∗
        (stackAt (sp - 48#64) Stage1X.extHookStack ∗
          ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
          ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right h2))

theorem tail_dealloc_post_48_extHook (v : BitVec 64) (Pool : SepProp) (sp : BitVec 64) :
    Pool ∗ stackAt sp Stage1X.extHookStack ∗ memRegion v 24 ∗ memRegion (sp - 16432#64) 48 ⊢
      memRegion v 24 ∗ Pool ∗ stackAt sp dropVecMessageKeyStackX := by
  rw [stackAt_dropVecMessageKeyX_split sp, ← tail_stack_48_from_bottom_ext sp]
  exact Entails.of_eq (by ac_rfl)

/-! ## Layout and deallocation helpers -/

theorem layoutOk_u8_x {cap : Nat} (h0 : cap ≠ 0) (hlt : cap < 2 ^ 63) : LayoutOk cap 1 :=
  ⟨by omega, ⟨0, rfl⟩, by omega⟩

theorem layoutOk_mul104_x {cap : Nat} (h0 : cap ≠ 0) (hlt : cap * 104 < 2 ^ 63) : LayoutOk (cap * 104) 8 :=
  ⟨by omega, ⟨3, rfl⟩, by omega⟩

/-- `vecPinDeallocX` preserves the upper bound `cap.toNat < 2^63` needed for `LayoutOk`. -/
def vecPinDeallocX (A : RustAlloc) (pin : VecPin) : SepProp :=
  if (pin.cap == 0#64) = true then emp
  else ⌜pin.cap.toNat < 2 ^ 63⌝ ∗ (A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat)

theorem vecU8At_entails_pin_deallocX (A : RustAlloc) (a : BitVec 64) (pin : VecPin)
    (bs : List (BitVec 8)) :
    vecU8At A a pin.cap pin.ptr bs ⊢
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDeallocX A pin := by
  refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr bs) ?_
  unfold vecHeader vecPinDeallocX
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hpure
  have hbeq : ((pin.cap == 0#64) = true) ↔ pin.cap = 0 := beq_iff_eq
  simp only [hbeq]
  have hgroup1 : ((a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      (if pin.cap = 0 then emp else A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat) =
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ (((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (if pin.cap = 0 then emp else A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat)) := by ac_rfl
  have hgroup2 : (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ memRegion (a + 16#64) 8 ∗
      (if pin.cap = 0 then emp else ⌜pin.cap.toNat < 2 ^ 63⌝ ∗ A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat) =
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ (memRegion (a + 16#64) 8 ∗
        (if pin.cap = 0 then emp else ⌜pin.cap.toNat < 2 ^ 63⌝ ∗ A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat)) := by ac_rfl
  rw [hgroup1, hgroup2]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
  by_cases hcap : pin.cap = 0
  · simp only [hcap, ite_true]
    exact Entails.refl _
  · simp only [hcap, ite_false]
    exact Entails.pure_right hpure.2.1 (Entails.refl _)

theorem messageKeyAt_entails_deallocX (A : RustAlloc) (cur : BitVec 64)
    (pin : MessageKeyGhost) (mk : MessageKeyGenerator) :
    messageKeyAt A (pin, mk) cur ⊢
      mkHeadersAt cur pin ∗
      vecPinDeallocX A pin.cipher ∗ vecPinDeallocX A pin.mac ∗
      vecPinDeallocX A pin.iv ∗ vecPinDeallocX A pin.seed := by
  unfold messageKeyAt mkHeadersAt
  apply Entails.pure_left; intro _
  have h1 := vecU8At_entails_pin_deallocX A cur pin.cipher []
  have h2 := vecU8At_entails_pin_deallocX A (cur + 24#64) pin.mac []
  have h3 := vecU8At_entails_pin_deallocX A (cur + 48#64) pin.iv []
  have h4 := vecU8At_entails_pin_deallocX A (cur + 72#64) pin.seed mk.seed
  have h5 : ((cur + 96#64) ↦₃₂ mk.counter) ∗ memRegion (cur + 100#64) 4 ⊢ memRegion (cur + 96#64) 8 := by
    rw [ProofLib.memRegion_split' (b := cur + 96#64) (n := 4) (k := 4)
          (b' := cur + 100#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (pointsTo32_entails_memRegion _ _)
  have ha1 : (cur + 24#64) + 8#64 = cur + 32#64 := by bv_omega
  have ha2 : (cur + 24#64) + 16#64 = cur + 40#64 := by bv_omega
  have hb1 : (cur + 48#64) + 8#64 = cur + 56#64 := by bv_omega
  have hb2 : (cur + 48#64) + 16#64 = cur + 64#64 := by bv_omega
  have hc1 : (cur + 72#64) + 8#64 = cur + 80#64 := by bv_omega
  have hc2 : (cur + 72#64) + 16#64 = cur + 88#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  rw [hc1, hc2] at h4
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 h5)))) ?_
  apply Entails.of_eq
  ac_rfl

theorem pure_and_entails_pure_sep_of_x {P P' Q : Prop} {R : SepProp}
    (h : P → P' ∧ Q) :
    ⌜P⌝ ∗ R ⊢ ⌜P'⌝ ∗ (⌜Q⌝ ∗ R) := by
  apply Entails.pure_left; intro hp; rcases h hp with ⟨hp', hq⟩
  exact Entails.pure_right hp' (Entails.pure_right hq (Entails.refl R))

theorem dealloc_ok_at_state_x' {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image}
    {entry : BitVec 64} {s : State}
    (hdealloc : subroutine_ok (SP2Ext b ext)
      (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>"))
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok (SP2Ext b ext)
      (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>"))
      { pre := fun (p, size, align) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = size ∧
            (s'.readReg64 .x2).toNat = align ∧ LayoutOk size align⌝ ∗
          A.live p size align ∗ memRegion p size ∗
          A.pool ∗ stackAt s'.sp Stage1X.extHookStack
        post := (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).post } := by
  refine subroutine_ok_mono_entails hdealloc (fun ⟨p, size, align⟩ s0 => ?_) (fun _ _ _ => Entails.refl _)
  dsimp only [Spec.inImage, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack]
  exact pure_and_entails_pure_sep_of_x fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

/-- Callee-saved registers outside `x19..x22, x29, x30` (which are spilled into `[fsp..fsp+48]`). -/
@[reducible]
private def Saved48Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem SepWP.align_pre_x {prog : Program} {target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (heq : P = P_mid)
    (h : SepWP prog target s P_mid (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) :=
  DropGlueFacts.align_pre heq h

theorem pull_pin_pure {φ : Prop} {P Q Rest : SepProp} :
    (P ∗ (⌜φ⌝ ∗ Q)) ∗ Rest = ⌜φ⌝ ∗ ((P ∗ Q) ∗ Rest) := by
  rw [ProofLib.sepConj_pure_left_comm, sepConj_assoc]

theorem SepWP.align_pre_gen {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P')
    (h : SepWP prog target s P' post) :
    SepWP prog target s P post :=
  heq ▸ h

theorem SepWP.seq_clean_inv {prog : Program} {img : Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      Q sm → img.FrozenLoaded sm → sm.symtab = img.symtab →
      SepWP prog target_pc sm P_mid post) :
    SepWP prog target_pc s P post :=
  CryptoVerification.SepWP.of_sepWP_inv (mid := mid) (target_pc := target_pc) hfl hsym
    (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hPm, hQ⟩ hfl' hsym' =>
      SepWP.weaken_pre hPm (h2 sm hpc hrun hQ hfl' hsym'))

theorem SepWP.finish_inv {prog : Program} {img : Obj.Image} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog target_pc s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → post sm Pm)) :
    SepWP prog target_pc s P post := by
  refine CryptoVerification.SepWP.of_sepWP_inv (mid := target_pc) (target_pc := target_pc) hfl hsym ?_
  exact SepWP.mono h (fun sm Pm hpc hrun hpost hfl' hsym' =>
    SepWP.done hpc hrun (hpost hfl' hsym'))

/-! ## Per-element loop body (`0x1f28`) -/

private theorem drop_vec_message_key_body_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropVecMessageKeyName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>"))
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).inImage img))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (pin : MessageKeyGhost) (mk : MessageKeyGenerator)
      (s : State) (Frame : SepProp),
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = (SP2Ext img.base ext).fnAddr dropVecMessageKeyName + 48#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP (SP2Ext img.base ext)
        ((SP2Ext img.base ext).fnAddr dropVecMessageKeyName + 36#64)
        s
        (messageKeyAt A (pin, mk) cur ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧
          sm.readReg64 .x22 = cur + 48#64 ∧
          img.FrozenLoaded sm ∧
          sm.symtab = img.symtab) := by
  have hfn : libsignalSessionCode.fnOff dropVecMessageKeyName = num% (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>")
  dsimp only [SP2Ext, contractProg, dropVecMessageKeyName, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>") (num% (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>")) 188
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>" = entry
  examples_hide_fetches
  intro cur cnt pin mk s Frame hfl hsym hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (messageKeyAt_entails_deallocX A cur pin mk)) ?_
  refine SepWP.seq_clean_inv (mid := entry + bv% (68)) (target_pc := entry + bv% (36)) hfl hsym
    (P_mid :=
      (mkHeadersAt cur pin ∗ vecPinDeallocX A pin.mac ∗ vecPinDeallocX A pin.iv ∗ vecPinDeallocX A pin.seed) ∗
      A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
    ?_ ?_
  · dsimp only [mkHeadersAt, vecPinDeallocX]
    by_cases hcap : (pin.cipher.cap == 0#64) = true
    · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      wp_done
    · simp only [hcap, ↓reduceIte]
      have hfalse : (false = true) ↔ False := by decide
      simp only [hfalse, ite_false]
      have heq_pure :
          (((cur ↦₆₄ pin.cipher.cap ∗
                (cur + 8#64) ↦₆₄ pin.cipher.ptr ∗
                  memRegion (cur + 16#64) 8 ∗
                    (cur + 24#64) ↦₆₄ pin.mac.cap ∗
                      (cur + 32#64) ↦₆₄ pin.mac.ptr ∗
                        memRegion (cur + 40#64) 8 ∗
                          (cur + 48#64) ↦₆₄ pin.iv.cap ∗
                            (cur + 56#64) ↦₆₄ pin.iv.ptr ∗
                              memRegion (cur + 64#64) 8 ∗
                                (cur + 72#64) ↦₆₄ pin.seed.cap ∗
                                  (cur + 80#64) ↦₆₄ pin.seed.ptr ∗ memRegion (cur + 88#64) 8 ∗ memRegion (cur + 96#64) 8) ∗
              (⌜pin.cipher.cap.toNat < 2 ^ 63⌝ ∗
                  A.live pin.cipher.ptr pin.cipher.cap.toNat 1 ∗ memRegion pin.cipher.ptr pin.cipher.cap.toNat) ∗
                (if (pin.mac.cap == 0#64) = true then emp
                  else
                    ⌜pin.mac.cap.toNat < 2 ^ 63⌝ ∗
                      A.live pin.mac.ptr pin.mac.cap.toNat 1 ∗ memRegion pin.mac.ptr pin.mac.cap.toNat) ∗
                  (if (pin.iv.cap == 0#64) = true then emp
                    else
                      ⌜pin.iv.cap.toNat < 2 ^ 63⌝ ∗
                        A.live pin.iv.ptr pin.iv.cap.toNat 1 ∗ memRegion pin.iv.ptr pin.iv.cap.toNat) ∗
                    if (pin.seed.cap == 0#64) = true then emp
                    else
                      ⌜pin.seed.cap.toNat < 2 ^ 63⌝ ∗
                        A.live pin.seed.ptr pin.seed.cap.toNat 1 ∗ memRegion pin.seed.ptr pin.seed.cap.toNat) ∗
            A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) =
          ⌜pin.cipher.cap.toNat < 2 ^ 63⌝ ∗
          (((cur ↦₆₄ pin.cipher.cap ∗
                (cur + 8#64) ↦₆₄ pin.cipher.ptr ∗
                  memRegion (cur + 16#64) 8 ∗
                    (cur + 24#64) ↦₆₄ pin.mac.cap ∗
                      (cur + 32#64) ↦₆₄ pin.mac.ptr ∗
                        memRegion (cur + 40#64) 8 ∗
                          (cur + 48#64) ↦₆₄ pin.iv.cap ∗
                            (cur + 56#64) ↦₆₄ pin.iv.ptr ∗
                              memRegion (cur + 64#64) 8 ∗
                                (cur + 72#64) ↦₆₄ pin.seed.cap ∗
                                  (cur + 80#64) ↦₆₄ pin.seed.ptr ∗ memRegion (cur + 88#64) 8 ∗ memRegion (cur + 96#64) 8) ∗
              (A.live pin.cipher.ptr pin.cipher.cap.toNat 1 ∗ memRegion pin.cipher.ptr pin.cipher.cap.toNat) ∗
                (if (pin.mac.cap == 0#64) = true then emp
                  else
                    ⌜pin.mac.cap.toNat < 2 ^ 63⌝ ∗
                      A.live pin.mac.ptr pin.mac.cap.toNat 1 ∗ memRegion pin.mac.ptr pin.mac.cap.toNat) ∗
                  (if (pin.iv.cap == 0#64) = true then emp
                    else
                      ⌜pin.iv.cap.toNat < 2 ^ 63⌝ ∗
                        A.live pin.iv.ptr pin.iv.cap.toNat 1 ∗ memRegion pin.iv.ptr pin.iv.cap.toNat) ∗
                    if (pin.seed.cap == 0#64) = true then emp
                    else
                      ⌜pin.seed.cap.toNat < 2 ^ 63⌝ ∗
                        A.live pin.seed.ptr pin.seed.cap.toNat 1 ∗ memRegion pin.seed.ptr pin.seed.cap.toNat) ∗
            A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) := by ac_rfl
      refine SepWP.align_pre_gen heq_pure ?_
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hcap_ne : pin.cipher.cap ≠ 0 := by
        intro hc; rw [hc] at hcap; revert hcap; decide
      have h0 : pin.cipher.cap.toNat ≠ 0 := by
        intro h; apply hcap_ne; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
      have hlayout : LayoutOk pin.cipher.cap.toNat 1 := layoutOk_u8_x h0 hcap_lt
      have hdealloc0 := dealloc_ok_at_state_x' (entry := entry) hdealloc hfl hsym
      dsimp only [SP2Ext, contractProg] at hdealloc0
      wp_steps
      have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      wp_call hdealloc0 (pin.cipher.ptr, pin.cipher.cap.toNat, 1)
      refine SepWP.align_pre_x (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩ hfl1 hsym1
    refine SepWP.seq_clean_inv (mid := entry + bv% (88)) (target_pc := entry + bv% (36)) hfl1 hsym1
      (P_mid :=
        (mkHeadersAt cur pin ∗ vecPinDeallocX A pin.iv ∗ vecPinDeallocX A pin.seed) ∗
        A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
      ?_ ?_
    · dsimp only [mkHeadersAt, vecPinDeallocX]
      by_cases hcap : (pin.mac.cap == 0#64) = true
      · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        wp_steps
        wp_done
      · simp only [hcap, ↓reduceIte]
        have hfalse : (false = true) ↔ False := by decide
        simp only [hfalse, ite_false]
        have heq_pure :
            (((cur ↦₆₄ pin.cipher.cap ∗
                  (cur + 8#64) ↦₆₄ pin.cipher.ptr ∗
                    memRegion (cur + 16#64) 8 ∗
                      (cur + 24#64) ↦₆₄ pin.mac.cap ∗
                        (cur + 32#64) ↦₆₄ pin.mac.ptr ∗
                          memRegion (cur + 40#64) 8 ∗
                            (cur + 48#64) ↦₆₄ pin.iv.cap ∗
                              (cur + 56#64) ↦₆₄ pin.iv.ptr ∗
                                memRegion (cur + 64#64) 8 ∗
                                  (cur + 72#64) ↦₆₄ pin.seed.cap ∗
                                    (cur + 80#64) ↦₆₄ pin.seed.ptr ∗ memRegion (cur + 88#64) 8 ∗ memRegion (cur + 96#64) 8) ∗
                (⌜pin.mac.cap.toNat < 2 ^ 63⌝ ∗
                    A.live pin.mac.ptr pin.mac.cap.toNat 1 ∗ memRegion pin.mac.ptr pin.mac.cap.toNat) ∗
                  (if (pin.iv.cap == 0#64) = true then emp
                    else
                      ⌜pin.iv.cap.toNat < 2 ^ 63⌝ ∗
                        A.live pin.iv.ptr pin.iv.cap.toNat 1 ∗ memRegion pin.iv.ptr pin.iv.cap.toNat) ∗
                  if (pin.seed.cap == 0#64) = true then emp
                  else
                    ⌜pin.seed.cap.toNat < 2 ^ 63⌝ ∗
                      A.live pin.seed.ptr pin.seed.cap.toNat 1 ∗ memRegion pin.seed.ptr pin.seed.cap.toNat) ∗
              A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) =
            ⌜pin.mac.cap.toNat < 2 ^ 63⌝ ∗
            (((cur ↦₆₄ pin.cipher.cap ∗
                  (cur + 8#64) ↦₆₄ pin.cipher.ptr ∗
                    memRegion (cur + 16#64) 8 ∗
                      (cur + 24#64) ↦₆₄ pin.mac.cap ∗
                        (cur + 32#64) ↦₆₄ pin.mac.ptr ∗
                          memRegion (cur + 40#64) 8 ∗
                            (cur + 48#64) ↦₆₄ pin.iv.cap ∗
                              (cur + 56#64) ↦₆₄ pin.iv.ptr ∗
                                memRegion (cur + 64#64) 8 ∗
                                  (cur + 72#64) ↦₆₄ pin.seed.cap ∗
                                    (cur + 80#64) ↦₆₄ pin.seed.ptr ∗ memRegion (cur + 88#64) 8 ∗ memRegion (cur + 96#64) 8) ∗
                (A.live pin.mac.ptr pin.mac.cap.toNat 1 ∗ memRegion pin.mac.ptr pin.mac.cap.toNat) ∗
                  (if (pin.iv.cap == 0#64) = true then emp
                    else
                      ⌜pin.iv.cap.toNat < 2 ^ 63⌝ ∗
                        A.live pin.iv.ptr pin.iv.cap.toNat 1 ∗ memRegion pin.iv.ptr pin.iv.cap.toNat) ∗
                  if (pin.seed.cap == 0#64) = true then emp
                  else
                    ⌜pin.seed.cap.toNat < 2 ^ 63⌝ ∗
                      A.live pin.seed.ptr pin.seed.cap.toNat 1 ∗ memRegion pin.seed.ptr pin.seed.cap.toNat) ∗
              A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) := by ac_rfl
        refine SepWP.align_pre_gen heq_pure ?_
        refine SepWP.pure_elim fun hcap_lt => ?_
        have hcap_ne : pin.mac.cap ≠ 0 := by
          intro hc; rw [hc] at hcap; revert hcap; decide
        have h0 : pin.mac.cap.toNat ≠ 0 := by
          intro h; apply hcap_ne; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
        have hlayout : LayoutOk pin.mac.cap.toNat 1 := layoutOk_u8_x h0 hcap_lt
        have hdealloc0 := dealloc_ok_at_state_x' (entry := entry) hdealloc hfl1 hsym1
        dsimp only [SP2Ext, contractProg] at hdealloc0
        wp_steps
        have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
        wp_call hdealloc0 (pin.mac.ptr, pin.mac.cap.toNat, 1)
        refine SepWP.align_pre_x (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩ hfl2 hsym2
      refine SepWP.seq_clean_inv (mid := entry + bv% (108)) (target_pc := entry + bv% (36)) hfl2 hsym2
        (P_mid :=
          (mkHeadersAt cur pin ∗ vecPinDeallocX A pin.seed) ∗
          A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
        ?_ ?_
      · dsimp only [mkHeadersAt, vecPinDeallocX]
        by_cases hcap : (pin.iv.cap == 0#64) = true
        · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          wp_steps
          wp_done
        · simp only [hcap, ↓reduceIte]
          have hfalse : (false = true) ↔ False := by decide
          simp only [hfalse, ite_false]
          have heq_pure :
              (((cur ↦₆₄ pin.cipher.cap ∗
                    (cur + 8#64) ↦₆₄ pin.cipher.ptr ∗
                      memRegion (cur + 16#64) 8 ∗
                        (cur + 24#64) ↦₆₄ pin.mac.cap ∗
                          (cur + 32#64) ↦₆₄ pin.mac.ptr ∗
                            memRegion (cur + 40#64) 8 ∗
                              (cur + 48#64) ↦₆₄ pin.iv.cap ∗
                                (cur + 56#64) ↦₆₄ pin.iv.ptr ∗
                                  memRegion (cur + 64#64) 8 ∗
                                    (cur + 72#64) ↦₆₄ pin.seed.cap ∗
                                      (cur + 80#64) ↦₆₄ pin.seed.ptr ∗ memRegion (cur + 88#64) 8 ∗ memRegion (cur + 96#64) 8) ∗
                  (⌜pin.iv.cap.toNat < 2 ^ 63⌝ ∗
                      A.live pin.iv.ptr pin.iv.cap.toNat 1 ∗ memRegion pin.iv.ptr pin.iv.cap.toNat) ∗
                  if (pin.seed.cap == 0#64) = true then emp
                  else
                    ⌜pin.seed.cap.toNat < 2 ^ 63⌝ ∗
                      A.live pin.seed.ptr pin.seed.cap.toNat 1 ∗ memRegion pin.seed.ptr pin.seed.cap.toNat) ∗
                A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) =
              ⌜pin.iv.cap.toNat < 2 ^ 63⌝ ∗
              (((cur ↦₆₄ pin.cipher.cap ∗
                    (cur + 8#64) ↦₆₄ pin.cipher.ptr ∗
                      memRegion (cur + 16#64) 8 ∗
                        (cur + 24#64) ↦₆₄ pin.mac.cap ∗
                          (cur + 32#64) ↦₆₄ pin.mac.ptr ∗
                            memRegion (cur + 40#64) 8 ∗
                              (cur + 48#64) ↦₆₄ pin.iv.cap ∗
                                (cur + 56#64) ↦₆₄ pin.iv.ptr ∗
                                  memRegion (cur + 64#64) 8 ∗
                                    (cur + 72#64) ↦₆₄ pin.seed.cap ∗
                                      (cur + 80#64) ↦₆₄ pin.seed.ptr ∗ memRegion (cur + 88#64) 8 ∗ memRegion (cur + 96#64) 8) ∗
                  (A.live pin.iv.ptr pin.iv.cap.toNat 1 ∗ memRegion pin.iv.ptr pin.iv.cap.toNat) ∗
                  if (pin.seed.cap == 0#64) = true then emp
                  else
                    ⌜pin.seed.cap.toNat < 2 ^ 63⌝ ∗
                      A.live pin.seed.ptr pin.seed.cap.toNat 1 ∗ memRegion pin.seed.ptr pin.seed.cap.toNat) ∗
                A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) := by ac_rfl
          refine SepWP.align_pre_gen heq_pure ?_
          refine SepWP.pure_elim fun hcap_lt => ?_
          have hcap_ne : pin.iv.cap ≠ 0 := by
            intro hc; rw [hc] at hcap; revert hcap; decide
          have h0 : pin.iv.cap.toNat ≠ 0 := by
            intro h; apply hcap_ne; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
          have hlayout : LayoutOk pin.iv.cap.toNat 1 := layoutOk_u8_x h0 hcap_lt
          have hdealloc0 := dealloc_ok_at_state_x' (entry := entry) hdealloc hfl2 hsym2
          dsimp only [SP2Ext, contractProg] at hdealloc0
          wp_steps
          have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
          wp_call hdealloc0 (pin.iv.ptr, pin.iv.cap.toNat, 1)
          refine SepWP.align_pre_x (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩ hfl3 hsym3
        have hstep4 : SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (entry + bv% (36)) s3
            ((mkHeadersAt cur pin ∗ vecPinDeallocX A pin.seed) ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ mkHeadersAt cur pin ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) := by
          dsimp only [mkHeadersAt, vecPinDeallocX]
          by_cases hcap : (pin.seed.cap == 0#64) = true
          · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
            wp_steps
            wp_done
          · simp only [hcap, ↓reduceIte]
            have hfalse : (false = true) ↔ False := by decide
            simp only [hfalse, ite_false]
            have heq_pure :
                (((cur ↦₆₄ pin.cipher.cap ∗
                      (cur + 8#64) ↦₆₄ pin.cipher.ptr ∗
                        memRegion (cur + 16#64) 8 ∗
                          (cur + 24#64) ↦₆₄ pin.mac.cap ∗
                            (cur + 32#64) ↦₆₄ pin.mac.ptr ∗
                              memRegion (cur + 40#64) 8 ∗
                                (cur + 48#64) ↦₆₄ pin.iv.cap ∗
                                  (cur + 56#64) ↦₆₄ pin.iv.ptr ∗
                                    memRegion (cur + 64#64) 8 ∗
                                      (cur + 72#64) ↦₆₄ pin.seed.cap ∗
                                        (cur + 80#64) ↦₆₄ pin.seed.ptr ∗ memRegion (cur + 88#64) 8 ∗ memRegion (cur + 96#64) 8) ∗
                    (⌜pin.seed.cap.toNat < 2 ^ 63⌝ ∗
                        A.live pin.seed.ptr pin.seed.cap.toNat 1 ∗ memRegion pin.seed.ptr pin.seed.cap.toNat)) ∗
                  A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) =
                ⌜pin.seed.cap.toNat < 2 ^ 63⌝ ∗
                (((cur ↦₆₄ pin.cipher.cap ∗
                      (cur + 8#64) ↦₆₄ pin.cipher.ptr ∗
                        memRegion (cur + 16#64) 8 ∗
                          (cur + 24#64) ↦₆₄ pin.mac.cap ∗
                            (cur + 32#64) ↦₆₄ pin.mac.ptr ∗
                              memRegion (cur + 40#64) 8 ∗
                                (cur + 48#64) ↦₆₄ pin.iv.cap ∗
                                  (cur + 56#64) ↦₆₄ pin.iv.ptr ∗
                                    memRegion (cur + 64#64) 8 ∗
                                      (cur + 72#64) ↦₆₄ pin.seed.cap ∗
                                        (cur + 80#64) ↦₆₄ pin.seed.ptr ∗ memRegion (cur + 88#64) 8 ∗ memRegion (cur + 96#64) 8) ∗
                    (A.live pin.seed.ptr pin.seed.cap.toNat 1 ∗ memRegion pin.seed.ptr pin.seed.cap.toNat)) ∗
                  A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) := by ac_rfl
            refine SepWP.align_pre_gen heq_pure ?_
            refine SepWP.pure_elim fun hcap_lt => ?_
            have hcap_ne : pin.seed.cap ≠ 0 := by
              intro hc; rw [hc] at hcap; revert hcap; decide
            have h0 : pin.seed.cap.toNat ≠ 0 := by
              intro h; apply hcap_ne; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
            have hlayout : LayoutOk pin.seed.cap.toNat 1 := layoutOk_u8_x h0 hcap_lt
            have hdealloc0 := dealloc_ok_at_state_x' (entry := entry) hdealloc hfl3 hsym3
            dsimp only [SP2Ext, contractProg] at hdealloc0
            wp_steps
            have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
            wp_call hdealloc0 (pin.seed.ptr, pin.seed.cap.toNat, 1)
            wp_steps
            refine SepWP.align_pre_x (by rw [hsp_3]; ac_rfl) ?_
            wp_done
        refine SepWP.finish_inv hfl3 hsym3 ?_
        refine SepWP.mono hstep4 (fun sm' Pm' _ _ h hfl' hsym' =>
          ⟨Entails.trans h.1 (sepConj_mono_left (mkHeadersAt_entails_memRegion_104 cur pin)),
           h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, hfl', hsym'⟩)


@[local simp] theorem frozenLoaded_writeReg64 {img : Obj.Image} {s : State} {r : Reg} {v : BitVec 64} :
    img.FrozenLoaded (s.writeReg64 r v) ↔ img.FrozenLoaded s :=
  ⟨fun h => frozenLoaded_of_mem_eq (s0 := s) (s := s.writeReg64 r v) rfl h,
   fun h => frozenLoaded_of_mem_eq (s0 := s.writeReg64 r v) (s := s) rfl h⟩

@[local simp] theorem frozenLoaded_setPState {img : Obj.Image} {s : State} {ps : PState} :
    img.FrozenLoaded (s.setPState ps) ↔ img.FrozenLoaded s :=
  ⟨fun h => frozenLoaded_of_mem_eq (s0 := s) (s := s.setPState ps) rfl h,
   fun h => frozenLoaded_of_mem_eq (s0 := s.setPState ps) (s := s) rfl h⟩

@[local simp] theorem frozenLoaded_setPC {img : Obj.Image} {s : State} {pc : BitVec 64} :
    img.FrozenLoaded (s.setPC pc) ↔ img.FrozenLoaded s :=
  ⟨fun h => frozenLoaded_of_mem_eq (s0 := s) (s := s.setPC pc) rfl h,
   fun h => frozenLoaded_of_mem_eq (s0 := s.setPC pc) (s := s) rfl h⟩

@[local simp] theorem symtab_writeReg64 {s : State} {r : Reg} {v : BitVec 64} :
    (s.writeReg64 r v).symtab = s.symtab := rfl

@[local simp] theorem symtab_setPState {s : State} {ps : PState} :
    (s.setPState ps).symtab = s.symtab := rfl

@[local simp] theorem symtab_setPC {s : State} {pc : BitVec 64} :
    (s.setPC pc).symtab = s.symtab := rfl

attribute [local arm64_norm] frozenLoaded_writeReg64 frozenLoaded_setPState frozenLoaded_setPC
attribute [local arm64_norm] symtab_writeReg64 symtab_setPState symtab_setPC

/-! ## Loop invariant stepping -/

private theorem drop_vec_message_key_loop_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropVecMessageKeyName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>"))
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).inImage img))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (MessageKeyGhost × MessageKeyGenerator)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (SP2Ext img.base ext).fnAddr dropVecMessageKeyName + 48#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP (SP2Ext img.base ext)
        ((SP2Ext img.base ext).fnAddr dropVecMessageKeyName + 132#64)
        s
        (arrayAt (messageKeyAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v ∧
          img.FrozenLoaded sm ∧
          sm.symtab = img.symtab) := by
  have hbody := drop_vec_message_key_body_ext hdealloc s0 fsp v ptr hfsp_align
  dsimp only [SP2Ext, contractProg, dropVecMessageKeyName, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>") (num% (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>")) 188
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨pin, mk⟩
    intro cur s Frame hfl hsym _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    rw [show arrayAt (messageKeyAt A) 104 cur ((pin, mk) :: tl) =
          messageKeyAt A (pin, mk) cur ∗ arrayAt (messageKeyAt A) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine SepWP.seq_clean_inv (mid := entry + bv% (36)) (target_pc := entry + bv% (132)) hfl hsym
      (hbody cur (BitVec.ofNat 64 ((pin, mk) :: tl).length) pin mk s
        (arrayAt (messageKeyAt A) 104 (cur + 104#64) tl ∗ Frame)
        hfl hsym hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4, hx21_4, hx22_4, hfl4, hsym4⟩ _ _
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx21_4 ⊢
      wp_steps
      wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show ((pin, mk) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx21_4
      have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
      wp_steps
      rw [sep_push_body]
      refine SepWP.mono
        (ih (cur + 104#64) _ (memRegion cur 104 ∗ Frame)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          htl_ne htl_len rfl (by assumption)
          ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
          hx19_4 hx20_4
          rfl
          (by simp only [wp_norm, arm64_norm, add_104_add_48])) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (pin, mk) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

/-! ## Top-level entry on `SP2Ext` -/

theorem drop_vec_message_key_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropVecMessageKeyName)
      ((dropVecMessageKeySpecX A).inImage img) := by
  have hdealloc_raw := hA.dealloc_ok_at (name := dropVecMessageKeyName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>")) (by simp only [arm64_norm])
  have hdealloc : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropVecMessageKeyName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>"))
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).inImage img) := hdealloc_raw
  have hloop := drop_vec_message_key_loop_ext (A := A) (img := img) (ext := ext) hdealloc
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>") (num% (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>")) 188
  dsimp only [SP2Ext, contractProg, dropVecMessageKeyName, BitVec.ofNat_eq_ofNat] at hdealloc hloop ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>" = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨v, cap, ptr, mks⟩ := x
  dsimp only at *
  subst h
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropVecMessageKeyX_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop A 104 8 (messageKeyAt A) (s0.readReg64 (Reg.gpr 0#5)) cap ptr mks)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine SepWP.seq_clean_inv (mid := entry + bv% (132)) (target_pc := s0.readReg64 .lr) h_2 h_1
    (P_mid :=
      (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 mks.length) ∗
      memRegion ptr (mks.length * 104) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (mks.length * 104)) ((cap.toNat - mks.length) * 104)) ∗
      A.pool ∗
      stackAt (s0.sp - 48#64) Stage1X.extHookStack ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = ptr ∧
      sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · cases mks with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
      wp_steps
      wp_done
    | cons hd tl =>
      have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
      refine SepWP.seq_clean_inv (mid := entry + bv% (48)) (target_pc := entry + bv% (132)) h_2 h_1
        (P_mid :=
          arrayAt (messageKeyAt A) 104 ptr (hd :: tl) ∗
          A.pool ∗ stackAt (s0.sp - 48#64) Stage1X.extHookStack ∗
          ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
            (if cap = 0 then emp
             else A.live ptr (cap.toNat * 104) 8 ∗
               memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 104)) ((cap.toNat - (hd :: tl).length) * 104)) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm =>
          Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5) ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (hd :: tl).length ∧
          sm.readReg64 .x22 = ptr + 48#64)
        ?_ ?_
      · wp_steps
        refine SepWP.done ?_ ?_ ?_
        · rfl
        · exact hrun
        · refine ⟨Entails.of_eq (by ac_rfl), ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
      · intro sm hpcm hrunm ⟨hpresm, hx19m, hx20m, hx21m, hx22m⟩ hfl_loop hsym_loop
        refine SepWP.mono
          (hloop s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) ptr hfsp_align (hd :: tl) ptr sm _
            hfl_loop hsym_loop
            (List.cons_ne_nil _ _) hlen_lt hpcm hrunm
            hpresm hx19m hx20m hx21m hx22m) ?_
        intro sf Pf _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2.1, h.2.2.1, h.2.2.2.1⟩
        apply Entails.of_eq
        ac_rfl
  · intro sm hpcm hrunm ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hx19, hx20⟩ hfl_m hsym_m
    refine SepWP.weaken_pre (post_loop_weaken A (s0.readReg64 (Reg.gpr 0#5)) cap ptr mks.length hlen_le hcap_lt _) ?_
    by_cases hcap : (cap == 0#64) = true
    · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine SepWP.weaken_pre (cap0_weaken_48_extHook (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · simp only [hcap, ↓reduceIte]
      have hcap_ne : cap ≠ 0 := by
        intro hc; rw [hc] at hcap; revert hcap; decide
      have h0 : cap.toNat ≠ 0 := by
        intro h; apply hcap_ne; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
      have hlayout : LayoutOk (cap.toNat * 104) 8 := layoutOk_mul104_x h0 hcap_lt
      have hdealloc0 := dealloc_ok_at_state_x' (entry := entry) hdealloc hfl_m hsym_m
      dsimp only [SP2Ext, contractProg] at hdealloc0
      wp_steps
      have hmul : 104#64 * cap = BitVec.ofNat 64 (cap.toNat * 104) := by bv_omega
      refine SepWP.weaken_pre
        (tail_dealloc_pre_weaken_ext (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ _ s0.sp _ _ _ _ _ _) ?_
      have : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
      wp_call hdealloc0 (ptr, cap.toNat * 104, 8)
      refine SepWP.weaken_pre (tail_dealloc_post_48_extHook (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done

/-! ## Relocatable `[LibsignalPlacement]` proofs (Block `3`) -/

section Placed

private theorem seq_clean_lscl_mk [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post := by
  apply sepWP_seq_lscl hcl (mid := mid)
  refine SepWP.mono h1 ?_
  rintro sm Pm hpcm hrunm ⟨hent, hQ⟩ hclm
  exact SepWP.weaken_pre hent (h2 sm hpcm hrunm hclm hQ)

private theorem expose_pin_deallocX_zero {A : RustAlloc} {pin : VecPin}
    (hcap : (pin.cap == 0#64) = true) :
    vecPinDeallocX A pin = emp := by
  unfold vecPinDeallocX; simp [hcap]

private theorem expose_pin_deallocX {A : RustAlloc} {pin : VecPin}
    (hcap : ¬ (pin.cap == 0#64) = true) :
    vecPinDeallocX A pin =
      ⌜pin.cap.toNat < 2 ^ 63⌝ ∗ (A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat) := by
  unfold vecPinDeallocX; simp [hcap]

private theorem pull_mk_pure4 {φ : Prop} {H P R1 R2 : SepProp} :
    (H ∗ (⌜φ⌝ ∗ P) ∗ R1) ∗ R2 = ⌜φ⌝ ∗ ((H ∗ P ∗ R1) ∗ R2) := by
  ac_rfl

private theorem pull_mk_pure3 {φ : Prop} {H P R2 : SepProp} :
    (H ∗ (⌜φ⌝ ∗ P)) ∗ R2 = ⌜φ⌝ ∗ ((H ∗ P) ∗ R2) := by
  ac_rfl

private theorem layoutOk_u8_of_ne_zero {cap : BitVec 64}
    (hcap : ¬ (cap == 0#64) = true) (hlt : cap.toNat < 2 ^ 63) :
    LayoutOk cap.toNat 1 := by
  apply layoutOk_u8_x _ hlt
  intro h0
  apply hcap
  have heq : cap = 0#64 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  subst heq; rfl

private theorem drop_vec_message_key_placed_body_ext [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((Getters.blkPC_3).rebase (Getters.blkPl_3).base H) (lsρ CryptoVerification.lsRustDeallocSym)
      (withLsCl lsmpl (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack)))
    (s0 : State) (fsp v ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (pin : MessageKeyGhost) (mk : MessageKeyGenerator) (s : State) (Frame : SepProp),
      s.pc = (Getters.blkPl_3).base + 48#64 → s.status = .Running → LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp → s.readReg64 .x19 = ptr → s.readReg64 .x20 = v →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 48#64 →
      SepWP ((Getters.blkPC_3).rebase (Getters.blkPl_3).base H) ((Getters.blkPl_3).base + 36#64) s
        (messageKeyAt A (pin, mk) cur ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) := by
  intro cur cnt pin mk s Frame hpc hrun hcl hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (messageKeyAt_entails_deallocX A cur pin mk)) ?_
  refine seq_clean_lscl_mk hcl (mid := (Getters.blkPl_3).base + 68#64) (P_mid :=
    (mkHeadersAt cur pin ∗ vecPinDeallocX A pin.mac ∗ vecPinDeallocX A pin.iv ∗ vecPinDeallocX A pin.seed) ∗
    A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) ?_ ?_
  · by_cases hcap : (pin.cipher.cap == 0#64) = true
    · conv => arg 4; rw [expose_pin_deallocX_zero hcap, emp_sepConj]; dsimp only [mkHeadersAt]
      dsimp only [mkHeadersAt]; wp_steps; wp_done
    · conv => arg 4; rw [expose_pin_deallocX hcap, pull_mk_pure4]; dsimp only [mkHeadersAt]
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hlayout := layoutOk_u8_of_ne_zero hcap hcap_lt
      apply sepWP_seq_lscl hcl (mid := lsρ CryptoVerification.lsRustDeallocSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
      have hcall := lscall_of_withLsCl hdealloc hcl_c
      have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      wp_call hcall (pin.cipher.ptr, pin.cipher.cap.toNat, 1)
      refine SepWP.align_pre_x (by dsimp only [mkHeadersAt]; rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
    refine seq_clean_lscl_mk hcl1 (mid := (Getters.blkPl_3).base + 88#64) (P_mid :=
      (mkHeadersAt cur pin ∗ vecPinDeallocX A pin.iv ∗ vecPinDeallocX A pin.seed) ∗
      A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) ?_ ?_
    · by_cases hcap : (pin.mac.cap == 0#64) = true
      · conv => arg 4; rw [expose_pin_deallocX_zero hcap, emp_sepConj]; dsimp only [mkHeadersAt]
        dsimp only [mkHeadersAt]; wp_steps; wp_done
      · conv => arg 4; rw [expose_pin_deallocX hcap, pull_mk_pure4]; dsimp only [mkHeadersAt]
        refine SepWP.pure_elim fun hcap_lt => ?_
        have hlayout := layoutOk_u8_of_ne_zero hcap hcap_lt
        apply sepWP_seq_lscl hcl1 (mid := lsρ CryptoVerification.lsRustDeallocSym)
        wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
        have hcall := lscall_of_withLsCl hdealloc hcl_c
        have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
        wp_call hcall (pin.mac.ptr, pin.mac.cap.toNat, 1)
        refine SepWP.align_pre_x (by dsimp only [mkHeadersAt]; rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine seq_clean_lscl_mk hcl2 (mid := (Getters.blkPl_3).base + 108#64) (P_mid :=
        (mkHeadersAt cur pin ∗ vecPinDeallocX A pin.seed) ∗
        A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) ?_ ?_
      · by_cases hcap : (pin.iv.cap == 0#64) = true
        · conv => arg 4; rw [expose_pin_deallocX_zero hcap, emp_sepConj]; dsimp only [mkHeadersAt]
          dsimp only [mkHeadersAt]; wp_steps; wp_done
        · conv => arg 4; rw [expose_pin_deallocX hcap, pull_mk_pure4]; dsimp only [mkHeadersAt]
          refine SepWP.pure_elim fun hcap_lt => ?_
          have hlayout := layoutOk_u8_of_ne_zero hcap hcap_lt
          apply sepWP_seq_lscl hcl2 (mid := lsρ CryptoVerification.lsRustDeallocSym)
          wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
          have hcall := lscall_of_withLsCl hdealloc hcl_c
          have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
          wp_call hcall (pin.iv.ptr, pin.iv.cap.toNat, 1)
          refine SepWP.align_pre_x (by dsimp only [mkHeadersAt]; rw [hsp_2]; ac_rfl) ?_
          wp_done
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        have hstep4 : SepWP ((Getters.blkPC_3).rebase (Getters.blkPl_3).base H)
            ((Getters.blkPl_3).base + 36#64) s3
            ((mkHeadersAt cur pin ∗ vecPinDeallocX A pin.seed) ∗
              A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ mkHeadersAt cur pin ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) := by
          by_cases hcap : (pin.seed.cap == 0#64) = true
          · conv => arg 4; rw [expose_pin_deallocX_zero hcap, sepConj_emp]; dsimp only [mkHeadersAt]
            dsimp only [mkHeadersAt]; wp_steps; wp_done
          · conv => arg 4; rw [expose_pin_deallocX hcap, pull_mk_pure3]; dsimp only [mkHeadersAt]
            refine SepWP.pure_elim fun hcap_lt => ?_
            have hlayout := layoutOk_u8_of_ne_zero hcap hcap_lt
            apply sepWP_seq_lscl hcl3 (mid := lsρ CryptoVerification.lsRustDeallocSym)
            wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
            have hcall := lscall_of_withLsCl hdealloc hcl_c
            have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
            wp_call hcall (pin.seed.ptr, pin.seed.cap.toNat, 1)
            wp_steps
            refine SepWP.align_pre_x (by dsimp only [mkHeadersAt]; rw [hsp_3]; ac_rfl) ?_
            wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (mkHeadersAt_entails_memRegion_104 cur pin)), h.2⟩)

private theorem drop_vec_message_key_placed_loop_ext [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((Getters.blkPC_3).rebase (Getters.blkPl_3).base H) (lsρ CryptoVerification.lsRustDeallocSym)
      (withLsCl lsmpl (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack)))
    (s0 : State) (fsp v ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (MessageKeyGhost × MessageKeyGenerator)) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 104 < 2 ^ 63 →
      s.pc = (Getters.blkPl_3).base + 48#64 → s.status = .Running → LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp → s.readReg64 .x19 = ptr → s.readReg64 .x20 = v →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 48#64 →
      SepWP ((Getters.blkPC_3).rebase (Getters.blkPl_3).base H) ((Getters.blkPl_3).base + 132#64) s
        (arrayAt (messageKeyAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v) := by
  have hbody := drop_vec_message_key_placed_body_ext hdealloc s0 fsp v ptr hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨pin, mk⟩
    intro cur s Frame _ hlen hpc hrun hcl hpres hx19 hx20 hx21 hx22
    rw [show arrayAt (messageKeyAt A) 104 cur ((pin, mk) :: tl) =
          messageKeyAt A (pin, mk) cur ∗ arrayAt (messageKeyAt A) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine seq_clean_lscl_mk hcl (mid := (Getters.blkPl_3).base + 36#64)
      (hbody cur (BitVec.ofNat 64 ((pin, mk) :: tl).length) pin mk s
        (arrayAt (messageKeyAt A) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hcl hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 hcl4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4, hx21_4, hx22_4⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx21_4 ⊢
      wp_steps; wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show ((pin, mk) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx21_4
      have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
      wp_steps
      rw [sep_push_body]
      refine SepWP.mono
        (ih (cur + 104#64) _ (memRegion cur 104 ∗ Frame)
          htl_ne htl_len rfl (by assumption) hcl4
          ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
          hx19_4 hx20_4 rfl
          (by simp only [wp_norm, arm64_norm, add_104_add_48])) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (pin, mk) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

/-- Relocatable `core::ptr::drop_glue::<Vec<session_structure::Chain::MessageKey>>` (Block `3`)
satisfies `withLsCodeLoaded lsmpl (dropVecMessageKeySpecX A)` under
`Stage1X.AllocContractsPlaced A H`. -/
theorem drop_vec_message_key_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    subroutine_ok ((Getters.blkPC_3).rebase (Getters.blkPl_3).base H)
      (Getters.blkPl_3).base
      (withLsCodeLoaded lsmpl (dropVecMessageKeySpecX A)) := by
  have hdealloc := hA.dealloc (callerProg := (Getters.blkPC_3).rebase (Getters.blkPl_3).base H)
  have hloop := drop_vec_message_key_placed_loop_ext hdealloc
  unfold withLsCodeLoaded dropVecMessageKeySpecX
  wp_init x s0
  obtain ⟨v, cap, ptr, mks⟩ := x
  dsimp only at *
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = v := by assumption
  subst hx0
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropVecMessageKeyX_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop A 104 8 (messageKeyAt A) (s0.readReg64 (Reg.gpr 0#5)) cap ptr mks)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine seq_clean_lscl_mk hcl0 (mid := (Getters.blkPl_3).base + 132#64)
    (P_mid :=
      (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 mks.length) ∗
      memRegion ptr (mks.length * 104) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (mks.length * 104)) ((cap.toNat - mks.length) * 104)) ∗
      A.pool ∗
      stackAt (s0.sp - 48#64) Stage1X.extHookStack ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = ptr ∧
      sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · cases mks with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
      wp_steps; wp_done
    | cons hd tl =>
      have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
      refine seq_clean_lscl_mk hcl0 (mid := (Getters.blkPl_3).base + 48#64)
        (P_mid :=
          arrayAt (messageKeyAt A) 104 ptr (hd :: tl) ∗
          A.pool ∗ stackAt (s0.sp - 48#64) Stage1X.extHookStack ∗
          ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
            (if cap = 0 then emp
             else A.live ptr (cap.toNat * 104) 8 ∗
               memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 104)) ((cap.toNat - (hd :: tl).length) * 104)) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm =>
          Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5) ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (hd :: tl).length ∧
          sm.readReg64 .x22 = ptr + 48#64)
        ?_ ?_
      · wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
        refine ⟨Entails.of_eq (by ac_rfl), ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
      · intro sm hpcm hrunm hcl_loop ⟨hpresm, hx19m, hx20m, hx21m, hx22m⟩
        refine SepWP.mono
          (hloop s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) ptr hfsp_align (hd :: tl) ptr sm _
            (List.cons_ne_nil _ _) hlen_lt hpcm hrunm hcl_loop
            hpresm hx19m hx20m hx21m hx22m) ?_
        intro sf Pf _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        exact Entails.of_eq (by ac_rfl)
  · intro sm hpcm hrunm hcl_m ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hx19, hx20⟩
    refine SepWP.weaken_pre (post_loop_weaken A (s0.readReg64 (Reg.gpr 0#5)) cap ptr mks.length hlen_le hcap_lt _) ?_
    by_cases hcap : (cap == 0#64) = true
    · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine SepWP.weaken_pre (cap0_weaken_48_extHook (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · simp only [hcap, ↓reduceIte]
      have hcap_ne : cap ≠ 0 := by
        intro hc; rw [hc] at hcap; revert hcap; decide
      have h0 : cap.toNat ≠ 0 := by
        intro h; apply hcap_ne; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
      have hlayout : LayoutOk (cap.toNat * 104) 8 := layoutOk_mul104_x h0 hcap_lt
      apply sepWP_seq_lscl hcl_m (mid := lsρ CryptoVerification.lsRustDeallocSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcl_tail
      have hdealloc0 := lscall_of_withLsCl
        (hA.dealloc (callerProg := (Getters.blkPC_3).rebase (Getters.blkPl_3).base H)) hcl_tail
      have hmul : 104#64 * cap = BitVec.ofNat 64 (cap.toNat * 104) := by bv_omega
      refine SepWP.weaken_pre
        (tail_dealloc_pre_weaken_ext (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ _ s0.sp _ _ _ _ _ _) ?_
      have : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
      wp_call hdealloc0 (ptr, cap.toNat * 104, 8)
      refine SepWP.weaken_pre (tail_dealloc_post_48_extHook (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done

theorem drop_vec_message_key_placed_ok_cl [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    subroutine_ok callerProg (lsmpl.base 3)
      (withLsCl lsmpl (dropVecMessageKeySpecX A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (drop_vec_message_key_placed_ok_ext hA)

end Placed

end Proofs.libsignal.Hooks2
