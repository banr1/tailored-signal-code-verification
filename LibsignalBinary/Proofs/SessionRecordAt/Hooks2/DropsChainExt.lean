/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropsMessageKeyExt
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.Common
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `drop_glue::<Vec<Chain>>` (`0x1e74`)

Verifies `core::ptr::drop_glue::<Vec<session_structure::Chain>>` (`0x1e74`, Block `2`) against
`dropVecChainSpecX A` at `dropVecChainStackX` on `SP2Ext` and under relocatable
`[LibsignalPlacement]`.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
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
attribute [local arm64_norm] frozenLoaded_writeReg64 frozenLoaded_setPState frozenLoaded_setPC
attribute [local arm64_norm] symtab_writeReg64 symtab_setPState symtab_setPC

theorem L1_DropsChainExt : True := trivial

/-- Stack budget for `drop_glue::<Vec<Chain>>` (`dropVecMessageKeyStackX + 48`). -/
abbrev dropVecChainStackX : Nat := dropVecMessageKeyStackX + 48

/-- Specification of `drop_glue::<Vec<Chain>>` at `dropVecChainStackX`. -/
def dropVecChainSpecX (A : RustAlloc) : Spec DropVecChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v⌝ ∗
      vecAt A 104 8 (chainAt A) x.v x.cap x.ptr x.cs ∗ A.pool ∗
      stackAt s.sp dropVecChainStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗ A.pool ∗ stackAt s0.sp dropVecChainStackX

/-! ## Stack helpers -/

theorem stackAt_dropVecChainX_split (sp : BitVec 64) :
    stackAt sp dropVecChainStackX =
      stackAt (sp - 48#64) dropVecMessageKeyStackX ∗ cells (sp - 48#64) 6 := by
  have h := LibsignalTripleRatchet.stackAt_split_cells sp dropVecMessageKeyStackX 6 (by decide)
  exact h

theorem stackAt_dropVecMessageKeyX_split_bottom (fsp : BitVec 64) :
    stackAt fsp dropVecMessageKeyStackX =
      memRegion (fsp - 16432#64) 48 ∗ stackAt fsp Stage1X.extHookStack := by
  have h := ProofLib.stackAt_split_bottom fsp Stage1X.extHookStack 48 (by decide)
  exact h

theorem tail_stack_96_from_bottom_ext (sp : BitVec 64) :
    memRegion (sp - 16480#64) 96 ∗ stackAt sp Stage1X.extHookStack =
      stackAt (sp - 48#64) dropVecMessageKeyStackX ∗ cells (sp - 48#64) 6 := by
  -- `extHookStack` is `2 ^ 14` (Mathlib `Monoid.npow`): `rw` cannot match `16480#64`; use defeq.
  have h : stackAt sp dropVecChainStackX =
      memRegion (sp - 16480#64) 96 ∗ stackAt sp Stage1X.extHookStack :=
    ProofLib.stackAt_split_bottom sp Stage1X.extHookStack 96 (by decide)
  rw [← h]
  exact stackAt_dropVecChainX_split sp

theorem cells6_vecChain_entails_stack_bottom_ext (sp : BitVec 64)
    (fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion (sp - 16480#64) 96 ∗ stackAt sp Stage1X.extHookStack := by
  rw [tail_stack_96_from_bottom_ext sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

theorem tail_dealloc_vecChain_pre_weaken_ext (v cap ptr : BitVec 64) (Live Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      Live ∗ Pool ∗
      stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    Pool ∗ Live ∗ stackAt sp Stage1X.extHookStack ∗
      (memRegion v 24 ∗ memRegion (sp - 16480#64) 96) := by
  refine Entails.trans (header24_weaken v cap ptr _) ?_
  have hstk := cells6_vecChain_entails_stack_bottom_ext sp fp lr x22 x21 x20 x19
  have hgroup :
      (memRegion v 24 ∗ Live ∗ Pool ∗
        stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      ((stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
          ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
          ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ∗
        (Pool ∗ Live ∗ memRegion v 24)) := by ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_left hstk) ?_
  apply Entails.of_eq
  ac_rfl

theorem vecChain_tail_dealloc_post_ext (v : BitVec 64) (Pool : SepProp) (sp : BitVec 64) :
    Pool ∗ stackAt sp Stage1X.extHookStack ∗ memRegion v 24 ∗ memRegion (sp - 16480#64) 96 ⊢
      memRegion v 24 ∗ Pool ∗ stackAt sp dropVecChainStackX := by
  have hgroup :
      Pool ∗ stackAt sp Stage1X.extHookStack ∗ memRegion v 24 ∗ memRegion (sp - 16480#64) 96 =
      memRegion v 24 ∗ Pool ∗ (memRegion (sp - 16480#64) 96 ∗ stackAt sp Stage1X.extHookStack) := by ac_rfl
  have h : stackAt sp dropVecChainStackX =
      memRegion (sp - 16480#64) 96 ∗ stackAt sp Stage1X.extHookStack :=
    ProofLib.stackAt_split_bottom sp Stage1X.extHookStack 96 (by decide)
  rw [hgroup, ← h]
  exact Entails.refl _

theorem cap0_weaken_48_vecChain_ext (v cap ptr : BitVec 64) (Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      Pool ∗ stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion v 24 ∗ Pool ∗ stackAt sp dropVecChainStackX := by
  refine Entails.trans (header24_weaken v cap ptr _) ?_
  have hcells := cells6_sub48_entails sp fp lr x22 x21 x20 x19
  have hgroup :
      (memRegion v 24 ∗ Pool ∗
        stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      ((memRegion v 24 ∗ Pool) ∗
        (stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
          (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
           ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
           ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)))) := by ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right hcells)) ?_
  rw [← stackAt_dropVecChainX_split sp]
  apply Entails.of_eq
  ac_rfl

/-! ## Deallocation and exposure helpers -/

@[reducible]
def ckDeallocX (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  if cap.slt 1#64 = true then emp
  else ⌜cap.toNat < 2 ^ 63⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat

theorem vecGhostAt_entails_pin_deallocX (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a ⊢
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDeallocX A ⟨g.cap, g.ptr⟩ :=
  vecU8At_entails_pin_deallocX A a ⟨g.cap, g.ptr⟩ g.bytes

theorem optChainKeyAt_entails_deallocX (A : RustAlloc) (pin : VecPin)
    (ck : Option ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin ck a ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 16 ∗
        ckDeallocX A cap ptr := by
  cases ck with
  | none =>
    unfold optChainKeyAt
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16)
          (b' := a + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (a + 8#64),
        sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right optChainKeyNone (Entails.sepExists_right ptr ?_)
    have hslt : optChainKeyNone.slt 1#64 = true := by decide
    simp only [ckDeallocX, hslt, ↓reduceIte, sepConj_emp]
    exact Entails.refl _
  | some c =>
    unfold optChainKeyAt
    have hvec : vecU8At A a pin.cap pin.ptr (keyToBytes32 c.key) ⊢
        (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          ckDeallocX A pin.cap pin.ptr := by
      refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr (keyToBytes32 c.key)) ?_
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader ckDeallocX
      simp only [slt_one_iff_eq_zero hcap_lt, sepConj_assoc]
      by_cases hc : pin.cap = 0
      · simp only [hc, ↓reduceIte, sepConj_emp, emp_sepConj]
        exact Entails.refl _
      · have hfalse : (pin.cap = 0) = False := eq_false hc
        have hslt_false : (pin.cap.slt 1#64 = true) = False := by
          apply eq_false; rw [slt_one_iff_eq_zero hcap_lt]; exact hc
        simp only [hfalse, hslt_false, ↓reduceIte]
        exact Entails.trans (Entails.pure_right hcap_lt (Entails.refl _)) (Entails.of_eq (by ac_rfl))
    refine Entails.trans (sepConj_mono_left hvec) ?_
    refine Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr ?_)
    have h16 :
        (((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4) ⊢
          memRegion (a + 16#64) 16 := by
      rw [ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8)
            (b' := a + 24#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := a + 24#64) (n := 4) (k := 4)
            (b' := a + 28#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (pointsTo32_entails_memRegion _ _))
    have hgroup :
        ((a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          ckDeallocX A pin.cap pin.ptr) ∗
        ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4 =
        ((a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          (((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
           ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4)) ∗
        ckDeallocX A pin.cap pin.ptr := by ac_rfl
    rw [hgroup]
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right h16))) ?_
    apply Entails.of_eq
    ac_rfl

theorem chainAt_entails_deallocX (A : RustAlloc) (a : BitVec 64)
    (g : ChainGhost) (c : ReceiverChain) :
    chainAt A (g, c) a ⊢
      ∃∗ ckCap : BitVec 64, ∃∗ ckPtr : BitVec 64,
        chainOuterHeadersAt a g ckCap ckPtr ∗
        vecPinDeallocX A ⟨g.srk.cap, g.srk.ptr⟩ ∗
        vecPinDeallocX A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDeallocX A ckCap ckPtr ∗
        vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) := by
  unfold chainAt chainOuterHeadersAt
  apply Entails.pure_left; intro _
  have h1 := vecGhostAt_entails_pin_deallocX A g.srk a
  have h2 := vecGhostAt_entails_pin_deallocX A g.priv (a + 24#64)
  have h3 := optChainKeyAt_entails_deallocX A g.ck c.chainKey (a + 72#64)
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hc1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have hc2 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hc1, hc2] at h3
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_right h3))) ?_
  rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ckCap
  rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ckPtr
  refine Entails.sepExists_right ckCap (Entails.sepExists_right ckPtr ?_)
  apply Entails.of_eq
  ac_rfl

/-! ## Callee adapters -/

theorem fnAddr_dropVecMessageKey_eq_dropVecChain_add_ext (img : Obj.Image)
    (ext : String → Option (State → State)) :
    (SP2Ext img.base ext).fnAddr dropVecMessageKeyName =
      (SP2Ext img.base ext).fnAddr dropVecChainName + 180#64 := by
  dsimp only [SP2Ext, contractProg, dropVecMessageKeyName, dropVecChainName]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>"), (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")]
  bv_omega

theorem drop_vec_message_key_ok_at_state_ext {prog : Program} {img : Obj.Image} {A : RustAlloc}
    {target : BitVec 64} {s : State}
    (hdrop_mk : subroutine_ok prog target
      ((dropVecMessageKeySpecX A).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok prog target
      { pre := fun x s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧ s'.readReg64 .x0 = x.v⌝ ∗
          vecAt A 104 8 (messageKeyAt A) x.v x.cap x.ptr x.mks ∗ A.pool ∗
          stackAt s'.sp dropVecMessageKeyStackX
        post := (dropVecMessageKeySpecX A).post } := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hm hsp => ?_
  refine hdrop_mk.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, dropVecMessageKeySpecX]
  exact pure_and_entails_pure_sep_of_x fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq (s0 := s0) (s := s) hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

theorem dealloc_ok_at_state_chain_ext {A : RustAlloc} {prog : Program} {img : Obj.Image}
    {target : BitVec 64} (s : State)
    (hdealloc : subroutine_ok prog target
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok prog target
      { pre := fun (p, size, align) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = size ∧
            (s'.readReg64 .x2).toNat = align ∧ LayoutOk size align⌝ ∗
          A.live p size align ∗ memRegion p size ∗
          A.pool ∗ stackAt s'.sp Stage1X.extHookStack
        post := (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).post } := by
  refine subroutine_ok_outcome_intro fun ⟨p, size, align⟩ R s0 hpc hrun hm hsp => ?_
  refine hdealloc.mono_outcome (p, size, align) R s0 hpc hrun ?_ hsp fun _ hout => hout
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack]
  exact pure_and_entails_pure_sep_of_x fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq (s0 := s0) (s := s) hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

theorem pull_srk_pure {g : ChainGhost} {ckCap ckPtr : BitVec 64} {A : RustAlloc} {cur : BitVec 64} {Rest : SepProp} :
    (((chainOuterHeadersAt cur g ckCap ckPtr ∗
       (⌜g.srk.cap.toNat < 2 ^ 63⌝ ∗ A.live g.srk.ptr g.srk.cap.toNat 1 ∗ memRegion g.srk.ptr g.srk.cap.toNat)) ∗
      vecPinDeallocX A ⟨g.priv.cap, g.priv.ptr⟩) ∗
     ckDeallocX A ckCap ckPtr) ∗ Rest =
    ⌜g.srk.cap.toNat < 2 ^ 63⌝ ∗
    ((((chainOuterHeadersAt cur g ckCap ckPtr ∗
       (A.live g.srk.ptr g.srk.cap.toNat 1 ∗ memRegion g.srk.ptr g.srk.cap.toNat)) ∗
      vecPinDeallocX A ⟨g.priv.cap, g.priv.ptr⟩) ∗
     ckDeallocX A ckCap ckPtr) ∗ Rest) := by
  ac_rfl

theorem pull_priv_pure {g : ChainGhost} {ckCap ckPtr : BitVec 64} {A : RustAlloc} {cur : BitVec 64} {Rest : SepProp} :
    ((chainOuterHeadersAt cur g ckCap ckPtr ∗
      (⌜g.priv.cap.toNat < 2 ^ 63⌝ ∗ A.live g.priv.ptr g.priv.cap.toNat 1 ∗ memRegion g.priv.ptr g.priv.cap.toNat)) ∗
     ckDeallocX A ckCap ckPtr) ∗ Rest =
    ⌜g.priv.cap.toNat < 2 ^ 63⌝ ∗
    (((chainOuterHeadersAt cur g ckCap ckPtr ∗
       (A.live g.priv.ptr g.priv.cap.toNat 1 ∗ memRegion g.priv.ptr g.priv.cap.toNat)) ∗
      ckDeallocX A ckCap ckPtr) ∗ Rest) := by
  ac_rfl

theorem pull_ck_pure {g : ChainGhost} {ckCap ckPtr : BitVec 64} {A : RustAlloc} {cur : BitVec 64} {Rest : SepProp} :
    (chainOuterHeadersAt cur g ckCap ckPtr ∗
     (⌜ckCap.toNat < 2 ^ 63⌝ ∗ A.live ckPtr ckCap.toNat 1 ∗ memRegion ckPtr ckCap.toNat)) ∗ Rest =
    ⌜ckCap.toNat < 2 ^ 63⌝ ∗
    ((chainOuterHeadersAt cur g ckCap ckPtr ∗
      (A.live ckPtr ckCap.toNat 1 ∗ memRegion ckPtr ckCap.toNat)) ∗ Rest) := by
  ac_rfl

theorem pull_pure_spine {φ : Prop} {P Q Rest : SepProp} :
    P ∗ ((⌜φ⌝ ∗ Q) ∗ Rest) = ⌜φ⌝ ∗ (P ∗ (Q ∗ Rest)) := by
  rw [sepConj_assoc, ProofLib.sepConj_pure_left_comm]

theorem SepWP.align_pre_chain {prog : Program} {target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (heq : P = P_mid)
    (h : SepWP prog target s P_mid (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) := by
  cases heq; exact h

/-! ## Per-element loop body (`0x1e74`) -/

private theorem drop_vec_chain_body_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropVecChainName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>"))
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).inImage img))
    (hdrop_mk : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropVecChainName + 180#64)
      ((dropVecMessageKeySpecX A).inImage img))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (g : ChainGhost) (c : ReceiverChain)
      (s : State) (Frame : SepProp),
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = (SP2Ext img.base ext).fnAddr dropVecChainName + 56#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 →
      s.readReg64 .x22 = cnt →
      SepWP (SP2Ext img.base ext)
        ((SP2Ext img.base ext).fnAddr dropVecChainName + 44#64)
        s
        (chainAt A (g, c) cur ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧
          sm.readReg64 .x22 = cnt ∧
          img.FrozenLoaded sm ∧
          sm.symtab = img.symtab) := by
  have hfn : libsignalSessionCode.fnOff dropVecChainName = num% (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") := (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")
  dsimp only [SP2Ext, contractProg, dropVecChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") (num% (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")) 180
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>" = entry
  examples_hide_fetches
  intro cur cnt g c s Frame hfl hsym hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (chainAt_entails_deallocX A cur g c)) ?_
  wp_pull_exists
  rename_i ckCap ckPtr
  rw [stackAt_dropVecMessageKeyX_split_bottom fsp]
  refine SepWP.seq_clean_inv (mid := entry + bv% (76)) (target_pc := entry + bv% (44)) hfl hsym
    (P_mid :=
      (chainOuterHeadersAt cur g ckCap ckPtr ∗
        vecPinDeallocX A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDeallocX A ckCap ckPtr) ∗
      A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
      (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
        memRegion (fsp - 16432#64) 48 ∗ Frame))
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt)
    ?_ ?_
  · dsimp only [chainOuterHeadersAt, vecPinDeallocX, ckDeallocX]
    by_cases hcap : (g.srk.cap == 0#64) = true
    · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine SepWP.align_pre_chain (by ac_rfl) ?_
      wp_done
    · have hcap_false : ((g.srk.cap == 0#64) = true) = False := eq_false hcap
      simp only [hcap_false, ↓reduceIte]
      simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hcap_ne : g.srk.cap.toNat ≠ 0 := by
        intro hc
        have h0 : g.srk.cap = 0#64 := BitVec.eq_of_toNat_eq (by rw [hc]; rfl)
        revert hcap
        simp [h0]
      have hlayout := layoutOk_u8_x hcap_ne hcap_lt
      have hdealloc0 := dealloc_ok_at_state_chain_ext s hdealloc hfl hsym
      wp_steps
      have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      wp_call hdealloc0 (g.srk.ptr, g.srk.cap.toNat, 1)
      refine SepWP.align_pre_chain (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩ hfl_1 hsym_1
    refine SepWP.seq_clean_inv (mid := entry + bv% (96)) (target_pc := entry + bv% (44)) hfl_1 hsym_1
      (P_mid :=
        (chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDeallocX A ckCap ckPtr) ∗
        A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
        (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
          memRegion (fsp - 16432#64) 48 ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt)
      ?_ ?_
    · dsimp only [chainOuterHeadersAt, vecPinDeallocX, ckDeallocX]
      by_cases hcap : (g.priv.cap == 0#64) = true
      · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        wp_steps
        refine SepWP.align_pre_chain (by ac_rfl) ?_
        wp_done
      · have hcap_false : ((g.priv.cap == 0#64) = true) = False := eq_false hcap
        simp only [hcap_false, ↓reduceIte]
        simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
        refine SepWP.pure_elim fun hcap_lt => ?_
        have hcap_ne : g.priv.cap.toNat ≠ 0 := by
          intro hc
          have h0 : g.priv.cap = 0#64 := BitVec.eq_of_toNat_eq (by rw [hc]; rfl)
          revert hcap
          simp [h0]
        have hlayout := layoutOk_u8_x hcap_ne hcap_lt
        have hdealloc0 := dealloc_ok_at_state_chain_ext s1 hdealloc hfl_1 hsym_1
        wp_steps
        have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
        wp_call hdealloc0 (g.priv.ptr, g.priv.cap.toNat, 1)
        refine SepWP.align_pre_chain (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩ hfl_2 hsym_2
      refine SepWP.seq_clean_inv (mid := entry + bv% (36)) (target_pc := entry + bv% (44)) hfl_2 hsym_2
        (P_mid :=
          vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
          A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗
          ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt)
        ?_ ?_
      · have hstep3 : SepWP (SP2Ext img.base ext) (entry + bv% (36)) s2
            ((chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDeallocX A ckCap ckPtr) ∗
              A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
              (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
                memRegion (fsp - 16432#64) 48 ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ chainOuterHeadersAt cur g ckCap ckPtr ∗
                A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
                (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
                  memRegion (fsp - 16432#64) 48 ∗ Frame)) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          dsimp only [chainOuterHeadersAt, ckDeallocX]
          by_cases hcap : ckCap.slt 1#64 = true
          · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
            wp_steps
            refine SepWP.align_pre_chain (by ac_rfl) ?_
            wp_done
          · have hcap_false : (ckCap.slt 1#64 = true) = False := eq_false hcap
            simp only [hcap_false, ↓reduceIte]
            simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
            refine SepWP.pure_elim fun hcap_lt => ?_
            have hcap_ne : ckCap.toNat ≠ 0 := by
              intro hc
              have h0 : ckCap = 0#64 := BitVec.eq_of_toNat_eq (by rw [hc]; rfl)
              rw [h0] at hcap
              exact hcap (by decide)
            have hlayout := layoutOk_u8_x hcap_ne hcap_lt
            have hdealloc0 := dealloc_ok_at_state_chain_ext s2 hdealloc hfl_2 hsym_2
            wp_steps
            have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
            wp_call hdealloc0 (ckPtr, ckCap.toNat, 1)
            wp_steps
            refine SepWP.align_pre_chain (by rw [hsp_2]; ac_rfl) ?_
            wp_done
        refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
        refine Entails.trans (sepConj_mono_left (chainOuterHeadersAt_entails_memRegions cur g ckCap ckPtr)) ?_
        rw [stackAt_dropVecMessageKeyX_split_bottom fsp]
        apply Entails.of_eq
        ac_rfl
      · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩ hfl_3 hsym_3
        rw [← stackAt_dropVecMessageKeyX_split_bottom fsp]
        have hdrop_mk0 := drop_vec_message_key_ok_at_state_ext hdrop_mk hfl_3 hsym_3
        refine SepWP.finish_inv hfl_3 hsym_3 ?_
        have hstep4 : SepWP (SP2Ext img.base ext) (entry + bv% (44)) s3
            (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
              A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗
              ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ (memRegion (cur + 48#64) 24 ∗ memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗
                A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          wp_steps
          wp_call hdrop_mk0 ⟨cur + 48#64, g.mkCap, g.mkPtr, g.keys.zip c.messageKeys⟩
          refine SepWP.align_pre_chain (by rw [hsp_3]; ac_rfl) ?_
          wp_done
        refine SepWP.mono hstep4 (fun sm Pm _ _ h hfl' hsym' =>
          ⟨Entails.trans h.1 (sepConj_mono_left (chain_memRegions_entails_104 cur)),
           h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, hfl', hsym'⟩)

/-! ## Loop invariant stepping -/

private theorem drop_vec_chain_loop_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropVecChainName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>"))
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).inImage img))
    (hdrop_mk : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropVecChainName + 180#64)
      ((dropVecMessageKeySpecX A).inImage img))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (ChainGhost × ReceiverChain)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (SP2Ext img.base ext).fnAddr dropVecChainName + 56#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      SepWP (SP2Ext img.base ext)
        ((SP2Ext img.base ext).fnAddr dropVecChainName + 124#64)
        s
        (arrayAt (chainAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v ∧
          img.FrozenLoaded sm ∧
          sm.symtab = img.symtab) := by
  have hbody := drop_vec_chain_body_ext hdealloc hdrop_mk s0 fsp v ptr hfsp_align
  dsimp only [SP2Ext, contractProg, dropVecChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") (num% (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")) 180
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨g, c⟩
    intro cur s Frame hfl hsym _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    rw [show arrayAt (chainAt A) 104 cur ((g, c) :: tl) =
          chainAt A (g, c) cur ∗ arrayAt (chainAt A) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine SepWP.seq_clean_inv (mid := entry + bv% (44)) (target_pc := entry + bv% (124)) hfl hsym
      (hbody cur (BitVec.ofNat 64 ((g, c) :: tl).length) g c s
        (arrayAt (chainAt A) 104 (cur + 104#64) tl ∗ Frame)
        hfl hsym hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4⟩, hx19_4, hx20_4, hx21_4, hx22_4, hfl4, hsym4⟩ _ _
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx22_4 ⊢
      wp_steps
      wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show ((g, c) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx22_4
      have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
      wp_steps
      rw [sep_push_body]
      refine SepWP.mono
        (ih (cur + 104#64) _ (memRegion cur 104 ∗ Frame)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          htl_ne htl_len rfl (by assumption)
          ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4⟩
          hx19_4 hx20_4
          (by simp only [wp_norm, arm64_norm, add_104_add_48])
          rfl) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (g, c) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

/-! ## Top-level entry on `SP2Ext` -/

theorem drop_vec_chain_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropVecChainName)
      ((dropVecChainSpecX A).inImage img) := by
  have hdealloc_raw := hA.dealloc_ok_at (name := dropVecChainName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")) (by simp only [arm64_norm])
  have hdealloc : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropVecChainName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>"))
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).inImage img) := hdealloc_raw
  have hdrop_mk_raw : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropVecChainName + 180#64)
      ((dropVecMessageKeySpecX A).inImage img) := by
    rw [← fnAddr_dropVecMessageKey_eq_dropVecChain_add_ext]
    exact drop_vec_message_key_ok_ext hA
  have hloop := drop_vec_chain_loop_ext (A := A) (img := img) (ext := ext) hdealloc hdrop_mk_raw
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") (num% (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")) 180
  dsimp only [SP2Ext, contractProg, dropVecChainName, BitVec.ofNat_eq_ofNat] at hdealloc hloop ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>" = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨v, cap, ptr, cs⟩ := x
  dsimp only at *
  subst h
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropVecChainX_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine SepWP.seq_clean_inv (mid := entry + bv% (124)) (target_pc := s0.readReg64 .lr) h_2 h_1
    (P_mid :=
      (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
      memRegion ptr (cs.length * 104) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) ∗
      A.pool ∗
      stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = ptr ∧
      sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · cases cs with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
      wp_steps
      refine SepWP.done ?_ ?_ ?_
      · rfl
      · exact hrun
      · refine ⟨Entails.refl _, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
    | cons hd tl =>
      have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
      refine SepWP.seq_clean_inv (mid := entry + bv% (56)) (target_pc := entry + bv% (124)) h_2 h_1
        (P_mid :=
          arrayAt (chainAt A) 104 ptr (hd :: tl) ∗
          A.pool ∗ stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
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
          sm.readReg64 .x21 = ptr + 48#64 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (hd :: tl).length)
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
    refine SepWP.weaken_pre (post_loop_weaken A (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs.length hlen_le hcap_lt _) ?_
    by_cases hcap : (cap == 0#64) = true
    · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine SepWP.weaken_pre (cap0_weaken_48_vecChain_ext (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · simp only [hcap, ↓reduceIte]
      have hcap_ne : cap ≠ 0 := by
        intro hc; rw [hc] at hcap; revert hcap; decide
      have h0 : cap.toNat ≠ 0 := by
        intro h; apply hcap_ne; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
      have hlayout : LayoutOk (cap.toNat * 104) 8 := layoutOk_mul104_x h0 hcap_lt
      have hdealloc0 := dealloc_ok_at_state_chain_ext sm hdealloc hfl_m hsym_m
      wp_steps
      have hmul : 104#64 * cap = BitVec.ofNat 64 (cap.toNat * 104) := by bv_omega
      refine SepWP.weaken_pre
        (tail_dealloc_vecChain_pre_weaken_ext (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ _ s0.sp _ _ _ _ _ _) ?_
      have : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
      wp_call hdealloc0 (ptr, cap.toNat * 104, 8)
      refine SepWP.weaken_pre (vecChain_tail_dealloc_post_ext (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done

/-! ## Relocatable `[LibsignalPlacement]` proofs (Block `2`) -/

section Placed

private theorem seq_clean_lscl_ch [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
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

private theorem expose_pin_deallocX_zero_ch {A : RustAlloc} {pin : VecPin}
    (hcap : (pin.cap == 0#64) = true) :
    vecPinDeallocX A pin = emp := by
  unfold vecPinDeallocX; simp [hcap]

private theorem expose_pin_deallocX_ch {A : RustAlloc} {pin : VecPin}
    (hcap : ¬ (pin.cap == 0#64) = true) :
    vecPinDeallocX A pin =
      ⌜pin.cap.toNat < 2 ^ 63⌝ ∗ (A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat) := by
  unfold vecPinDeallocX; simp [hcap]

private theorem expose_ckDeallocX_zero {A : RustAlloc} {ckCap ckPtr : BitVec 64}
    (hcap : ckCap.slt 1#64 = true) :
    ckDeallocX A ckCap ckPtr = emp := by
  unfold ckDeallocX; simp [hcap]

private theorem expose_ckDeallocX_ne {A : RustAlloc} {ckCap ckPtr : BitVec 64}
    (hcap : ¬ ckCap.slt 1#64 = true) :
    ckDeallocX A ckCap ckPtr =
      ⌜ckCap.toNat < 2 ^ 63⌝ ∗ (A.live ckPtr ckCap.toNat 1 ∗ memRegion ckPtr ckCap.toNat) := by
  unfold ckDeallocX; simp [hcap]

private theorem pull_ch_pure3 {φ : Prop} {H P R2 : SepProp} :
    (H ∗ (⌜φ⌝ ∗ P)) ∗ R2 = ⌜φ⌝ ∗ ((H ∗ P) ∗ R2) := by
  ac_rfl

private theorem layoutOk_u8_of_ne_zero_ch {cap : BitVec 64}
    (hcap : ¬ (cap == 0#64) = true) (hlt : cap.toNat < 2 ^ 63) :
    LayoutOk cap.toNat 1 := by
  apply layoutOk_u8_x _ hlt
  intro h0
  apply hcap
  have heq : cap = 0#64 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  subst heq; rfl

private theorem layoutOk_u8_of_not_slt1 {ckCap : BitVec 64}
    (hcap : ¬ ckCap.slt 1#64 = true) (hlt : ckCap.toNat < 2 ^ 63) :
    LayoutOk ckCap.toNat 1 := by
  apply layoutOk_u8_x _ hlt
  intro h0
  have heq : ckCap = 0#64 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  rw [heq] at hcap
  exact hcap (by decide)

private theorem drop_vec_chain_placed_body_ext [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((Getters.blkPC_2).rebase (Getters.blkPl_2).base H)
      (lsρ CryptoVerification.lsRustDeallocSym)
      (withLsCl lsmpl (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack)))
    (hdrop_mk : subroutine_ok ((Getters.blkPC_2).rebase (Getters.blkPl_2).base H)
      (lsmpl.base 3) (withLsCl lsmpl (dropVecMessageKeySpecX A)))
    (s0 : State) (fsp v ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (g : ChainGhost) (c : ReceiverChain) (s : State) (Frame : SepProp),
      s.pc = (Getters.blkPl_2).base + 56#64 → s.status = .Running → LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp → s.readReg64 .x19 = ptr → s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 → s.readReg64 .x22 = cnt →
      SepWP ((Getters.blkPC_2).rebase (Getters.blkPl_2).base H) ((Getters.blkPl_2).base + 44#64) s
        (chainAt A (g, c) cur ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
  intro cur cnt g c s Frame hpc hrun hcl hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (chainAt_entails_deallocX A cur g c)) ?_
  wp_pull_exists
  rename_i ckCap ckPtr
  rw [stackAt_dropVecMessageKeyX_split_bottom fsp]
  refine seq_clean_lscl_ch hcl (mid := (Getters.blkPl_2).base + 76#64)
    (P_mid :=
      (chainOuterHeadersAt cur g ckCap ckPtr ∗
        vecPinDeallocX A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDeallocX A ckCap ckPtr) ∗
      A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
      (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
        memRegion (fsp - 16432#64) 48 ∗ Frame))
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) ?_ ?_
  · by_cases hcap : (g.srk.cap == 0#64) = true
    · conv => arg 4; rw [expose_pin_deallocX_zero_ch (pin := ⟨g.srk.cap, g.srk.ptr⟩) hcap, emp_sepConj]
      wp_steps
      refine SepWP.align_pre_chain (by dsimp only [chainOuterHeadersAt]; try ac_rfl) ?_
      wp_done
    · conv => arg 4; rw [expose_pin_deallocX_ch (pin := ⟨g.srk.cap, g.srk.ptr⟩) hcap]; simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hlayout := layoutOk_u8_of_ne_zero_ch hcap hcap_lt
      apply sepWP_seq_lscl hcl (mid := lsρ CryptoVerification.lsRustDeallocSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
      have hcall := lscall_of_withLsCl hdealloc hcl_c
      have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      wp_call hcall (g.srk.ptr, g.srk.cap.toNat, 1)
      refine SepWP.align_pre_chain (by dsimp only [chainOuterHeadersAt]; rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
    refine seq_clean_lscl_ch hcl1 (mid := (Getters.blkPl_2).base + 96#64)
      (P_mid :=
        (chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDeallocX A ckCap ckPtr) ∗
        A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
        (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
          memRegion (fsp - 16432#64) 48 ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) ?_ ?_
    · by_cases hcap : (g.priv.cap == 0#64) = true
      · conv => arg 4; rw [expose_pin_deallocX_zero_ch (pin := ⟨g.priv.cap, g.priv.ptr⟩) hcap, emp_sepConj]; dsimp only [chainOuterHeadersAt]
        wp_steps
        refine SepWP.align_pre_chain (by dsimp only [chainOuterHeadersAt]; try ac_rfl) ?_
        wp_done
      · conv => arg 4; rw [expose_pin_deallocX_ch (pin := ⟨g.priv.cap, g.priv.ptr⟩) hcap]; dsimp only [chainOuterHeadersAt]; simp only [sepConj_assoc, ProofLib.sepConj_pure_left_comm]
        refine SepWP.pure_elim fun hcap_lt => ?_
        have hlayout := layoutOk_u8_of_ne_zero_ch hcap hcap_lt
        apply sepWP_seq_lscl hcl1 (mid := lsρ CryptoVerification.lsRustDeallocSym)
        wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
        have hcall := lscall_of_withLsCl hdealloc hcl_c
        have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
        wp_call hcall (g.priv.ptr, g.priv.cap.toNat, 1)
        refine SepWP.align_pre_chain (by dsimp only [chainOuterHeadersAt]; rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine seq_clean_lscl_ch hcl2 (mid := (Getters.blkPl_2).base + 36#64)
        (P_mid :=
          vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
          A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗
          ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) ?_ ?_
      · have hstep3 : SepWP ((Getters.blkPC_2).rebase (Getters.blkPl_2).base H)
            ((Getters.blkPl_2).base + 36#64) s2
            ((chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDeallocX A ckCap ckPtr) ∗
              A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
              (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
                memRegion (fsp - 16432#64) 48 ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ chainOuterHeadersAt cur g ckCap ckPtr ∗
                A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
                (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
                  memRegion (fsp - 16432#64) 48 ∗ Frame)) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          by_cases hcap : ckCap.slt 1#64 = true
          · conv => arg 4; rw [expose_ckDeallocX_zero hcap, sepConj_emp]; dsimp only [chainOuterHeadersAt]
            wp_steps
            refine SepWP.align_pre_chain (by dsimp only [chainOuterHeadersAt]; try ac_rfl) ?_
            wp_done
          · conv => arg 4; rw [expose_ckDeallocX_ne hcap, pull_ch_pure3]; dsimp only [chainOuterHeadersAt]
            refine SepWP.pure_elim fun hcap_lt => ?_
            have hlayout := layoutOk_u8_of_not_slt1 hcap hcap_lt
            apply sepWP_seq_lscl hcl2 (mid := lsρ CryptoVerification.lsRustDeallocSym)
            wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c
            have hcall := lscall_of_withLsCl hdealloc hcl_c
            have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
            wp_call hcall (ckPtr, ckCap.toNat, 1)
            wp_steps
            refine SepWP.align_pre_chain (by dsimp only [chainOuterHeadersAt]; rw [hsp_2]; ac_rfl) ?_
            wp_done
        refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
        refine Entails.trans (sepConj_mono_left (chainOuterHeadersAt_entails_memRegions cur g ckCap ckPtr)) ?_
        rw [stackAt_dropVecMessageKeyX_split_bottom fsp]
        exact Entails.of_eq (by ac_rfl)
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        rw [← stackAt_dropVecMessageKeyX_split_bottom fsp]
        have hstep4 : SepWP ((Getters.blkPC_2).rebase (Getters.blkPl_2).base H)
            ((Getters.blkPl_2).base + 44#64) s3
            (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
              A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗
              ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ (memRegion (cur + 48#64) 24 ∗ memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗
                A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          apply sepWP_seq_lscl hcl3 (mid := lsmpl.base 3)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro hcl_mk
          have hcall_mk := lscall_of_withLsCl hdrop_mk hcl_mk
          wp_call hcall_mk ⟨cur + 48#64, g.mkCap, g.mkPtr, g.keys.zip c.messageKeys⟩
          refine SepWP.align_pre_chain (by rw [hsp_3]; ac_rfl) ?_
          wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (chain_memRegions_entails_104 cur)), h.2⟩)

private theorem drop_vec_chain_placed_loop_ext [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((Getters.blkPC_2).rebase (Getters.blkPl_2).base H)
      (lsρ CryptoVerification.lsRustDeallocSym)
      (withLsCl lsmpl (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack)))
    (hdrop_mk : subroutine_ok ((Getters.blkPC_2).rebase (Getters.blkPl_2).base H)
      (lsmpl.base 3) (withLsCl lsmpl (dropVecMessageKeySpecX A)))
    (s0 : State) (fsp v ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (ChainGhost × ReceiverChain)) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 104 < 2 ^ 63 →
      s.pc = (Getters.blkPl_2).base + 56#64 → s.status = .Running → LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp → s.readReg64 .x19 = ptr → s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 → s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      SepWP ((Getters.blkPC_2).rebase (Getters.blkPl_2).base H) ((Getters.blkPl_2).base + 124#64) s
        (arrayAt (chainAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v) := by
  have hbody := drop_vec_chain_placed_body_ext hdealloc hdrop_mk s0 fsp v ptr hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨g, c⟩
    intro cur s Frame _ hlen hpc hrun hcl hpres hx19 hx20 hx21 hx22
    rw [show arrayAt (chainAt A) 104 cur ((g, c) :: tl) =
          chainAt A (g, c) cur ∗ arrayAt (chainAt A) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine seq_clean_lscl_ch hcl (mid := (Getters.blkPl_2).base + 44#64)
      (hbody cur (BitVec.ofNat 64 ((g, c) :: tl).length) g c s
        (arrayAt (chainAt A) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hcl hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 hcl4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4, hx21_4, hx22_4⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx22_4 ⊢
      wp_steps; wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show ((g, c) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx22_4
      have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
      wp_steps
      rw [sep_push_body]
      refine SepWP.mono
        (ih (cur + 104#64) _ (memRegion cur 104 ∗ Frame)
          htl_ne htl_len rfl (by assumption) hcl4
          ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
          hx19_4 hx20_4
          (by simp only [wp_norm, arm64_norm, add_104_add_48]) rfl) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (g, c) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

/-- Relocatable `core::ptr::drop_glue::<Vec<session_structure::Chain>>` (Block `2`) satisfies
`withLsCodeLoaded lsmpl (dropVecChainSpecX A)` under `Stage1X.AllocContractsPlaced A H`. -/
theorem drop_vec_chain_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    subroutine_ok ((Getters.blkPC_2).rebase (Getters.blkPl_2).base H)
      (Getters.blkPl_2).base
      (withLsCodeLoaded lsmpl (dropVecChainSpecX A)) := by
  have hdealloc := hA.dealloc (callerProg := (Getters.blkPC_2).rebase (Getters.blkPl_2).base H)
  have hdrop_mk := drop_vec_message_key_placed_ok_cl
    (callerProg := (Getters.blkPC_2).rebase (Getters.blkPl_2).base H) hA
  have hloop := drop_vec_chain_placed_loop_ext hdealloc hdrop_mk
  unfold withLsCodeLoaded dropVecChainSpecX
  wp_init x s0
  obtain ⟨v, cap, ptr, cs⟩ := x
  dsimp only at *
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = v := by assumption
  subst hx0
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropVecChainX_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine seq_clean_lscl_ch hcl0 (mid := (Getters.blkPl_2).base + 124#64)
    (P_mid :=
      (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
      memRegion ptr (cs.length * 104) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) ∗
      A.pool ∗
      stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = ptr ∧
      sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · cases cs with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
      wp_steps; wp_done
    | cons hd tl =>
      have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
      refine seq_clean_lscl_ch hcl0 (mid := (Getters.blkPl_2).base + 56#64)
        (P_mid :=
          arrayAt (chainAt A) 104 ptr (hd :: tl) ∗
          A.pool ∗ stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
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
          sm.readReg64 .x21 = ptr + 48#64 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (hd :: tl).length)
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
    refine SepWP.weaken_pre (post_loop_weaken A (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs.length hlen_le hcap_lt _) ?_
    by_cases hcap : (cap == 0#64) = true
    · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine SepWP.weaken_pre (cap0_weaken_48_vecChain_ext (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ s0.sp _ _ _ _ _ _) ?_
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
        (hA.dealloc (callerProg := (Getters.blkPC_2).rebase (Getters.blkPl_2).base H)) hcl_tail
      have hmul : 104#64 * cap = BitVec.ofNat 64 (cap.toNat * 104) := by bv_omega
      refine SepWP.weaken_pre
        (tail_dealloc_vecChain_pre_weaken_ext (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ _ s0.sp _ _ _ _ _ _) ?_
      have : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
      wp_call hdealloc0 (ptr, cap.toNat * 104, 8)
      refine SepWP.weaken_pre (vecChain_tail_dealloc_post_ext (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done

theorem drop_vec_chain_placed_ok_cl [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    subroutine_ok callerProg (lsmpl.base 2)
      (withLsCl lsmpl (dropVecChainSpecX A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (drop_vec_chain_placed_ok_ext hA)

end Placed

end Proofs.libsignal.Hooks2
