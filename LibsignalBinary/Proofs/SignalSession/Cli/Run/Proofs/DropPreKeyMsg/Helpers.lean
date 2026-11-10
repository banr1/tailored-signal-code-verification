/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalPublicApiRepr
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Specifications.AsmConstants
import ProofLib.SepLogic.WPp

/-!
# Exact-Stack Symbolic Execution for `PreKeySignalMessage` Drop Glue

Decomposes `preKeyMsgAt` (248 bytes) into deallocatable slice capabilities and proves
`dropPreKeyMsgExact_ok` for `core::ptr::drop_glue::<PreKeySignalMessage>` at stack budget
`32 + extHookStack`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.DropPreKeyMsgHelpers

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli

gen_decodes CryptoVerification.libsignalSessionCode_tree pkmDec
  [(ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>") →
   (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>" + 160)]

attribute [local irreducible] Program.fetch Program.externAt?

@[local wp_norm] private theorem exists_two_pow_one : (∃ k : Nat, 1 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨0, rfl⟩

/-! ## Stack and framing helpers -/

theorem stackAt_split_top (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = stackAt (sp - BitVec.ofNat 64 d) n ∗ memRegion (sp - BitVec.ofNat 64 d) d := by
  simp only [stackAt]
  rw [memRegion_split' (n := n) (k := d) rfl rfl h]
  have e1 : sp - BitVec.ofNat 64 (n + d) = sp - BitVec.ofNat 64 d - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  rw [e1, BitVec.sub_add_cancel]

/-- Frames and weakens a `subroutine_ok` specification across ghost projection `f` and frame `F`. -/
theorem subroutine_ok_map_frame_weaken {α β : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {spec' : Spec β} (f : β → α) (F : β → State → SepProp)
    (h : subroutine_ok prog entry spec)
    (hpre : ∀ x s0, spec'.pre x s0 ⊢ spec.pre (f x) s0 ∗ F x s0)
    (hpost : ∀ x s0 sf, spec.post (f x) s0 sf ∗ F x s0 ⊢ spec'.post x s0 sf)
    (hpan : ∀ x s0 sf, spec.onPanic (f x) s0 sf ∗ F x s0 ⊢ spec'.onPanic x s0 sf)
    (hexit : ∀ x code s0 sf, spec.onExit (f x) code s0 sf = ⌜False⌝)
    (hoom : ∀ x s0 sf, spec.onOom (f x) s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok prog entry spec' := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hp hsp
  have hp' : s0.mem ⊨ spec.pre (f x) s0 ∗ (F x s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre x s0)) hp
  refine h.mono_outcome (f x) (F x s0 ∗ R) s0 hpc hrun hp' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan_st, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hq
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpan x s0 sf)) hq
  · rw [hexit] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · rw [hoom] at hq
    exact (not_satisfies_false_sepConj hq).elim

private theorem stackAt_pkm_split (sp : BitVec 64) :
    stackAt sp (32 + extHookStack) =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

private theorem tail_stack_32_from_bottomX (sp : BitVec 64) :
    memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 := by
  rw [show (16416#64 : BitVec 64) = BitVec.ofNat 64 (extHookStack + 32) from rfl,
      ← ProofLib.stackAt_split_bottom sp extHookStack 32 (by decide),
      show extHookStack + 32 = 32 + extHookStack from rfl,
      ← stackAt_pkm_split sp]

private theorem cells4_entails_stack_bottomX (sp fp lr x19 c3 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ c3) ⊢
    memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack := by
  rw [tail_stack_32_from_bottomX sp]
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x19 (Entails.sepExists_right c3 (Entails.refl _))))

private theorem stack_restore_32X (sp fp lr x19 c3 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ c3) ⊢
    stackAt sp (32 + extHookStack) := by
  rw [stackAt_pkm_split sp, ← tail_stack_32_from_bottomX sp]
  exact cells4_entails_stack_bottomX sp fp lr x19 c3

/-! ## Heap decomposition for `PreKeySignalMessage` -/

def sliceDeallocX (A : RustAlloc) (ptr sz : BitVec 64) : SepProp :=
  if (sz == 0#64) = true then emp
  else ⌜0 < sz.toNat ∧ sz.toNat < 2 ^ 63⌝ ∗ A.live ptr sz.toNat 1 ∗ memRegion ptr sz.toNat

private theorem sliceDeallocX_eq (A : RustAlloc) (ptr sz : BitVec 64) :
    sliceDeallocX A ptr sz =
      if (sz == 0#64) = true then emp
      else ⌜0 < sz.toNat ∧ sz.toNat < 2 ^ 63⌝ ∗ A.live ptr sz.toNat 1 ∗ memRegion ptr sz.toNat :=
  rfl

def optSliceDeallocX (A : RustAlloc) (ptr sz : BitVec 64) : SepProp :=
  if (ptr == 0#64) = true then emp else sliceDeallocX A ptr sz

private theorem optSliceDeallocX_eq (A : RustAlloc) (ptr sz : BitVec 64) :
    optSliceDeallocX A ptr sz =
      if (ptr == 0#64) = true then emp else sliceDeallocX A ptr sz :=
  rfl

theorem boxU8At_entails_sliceDeallocX (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8At A a ptr bs ⊢
      (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ⌜ptr ≠ 0⌝ ∗ sliceDeallocX A ptr (BitVec.ofNat 64 bs.length) := by
  unfold boxU8At sliceDeallocX
  have h1 : (a + asm64% boxSliceLenOff) = a + 8#64 := rfl
  rw [h1]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  apply Entails.pure_left; rintro ⟨hptr, hlen⟩
  refine Entails.pure_right hptr ?_
  cases bs with
  | nil =>
    simp only [List.length_nil, ↓reduceIte]
    exact Entails.refl _
  | cons b tl =>
    have hpos : 0 < (b :: tl).length := by simp
    have hlt64 : (b :: tl).length < 2 ^ 64 := by omega
    have htoNat : (BitVec.ofNat 64 (b :: tl).length).toNat = (b :: tl).length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
    have hbeq : (BitVec.ofNat 64 (b :: tl).length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr fun h => by rw [h] at htoNat; simp at htoNat
    have hne : b :: tl ≠ [] := List.cons_ne_nil _ _
    simp only [hne, hbeq, Bool.false_eq_true, ↓reduceIte, htoNat]
    refine Entails.pure_right ⟨hpos, hlen⟩ ?_
    exact sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion ptr (b :: tl))

theorem optBoxU8At_entails_optSliceDeallocX (A : RustAlloc) (a ptr : BitVec 64)
    (optBs : Option (List (BitVec 8))) :
    optBoxU8At A a ptr optBs ⊢
      ∃∗ p : BitVec 64, ∃∗ l : BitVec 64,
        (a ↦₆₄ p) ∗ ((a + 8#64) ↦₆₄ l) ∗ optSliceDeallocX A p l := by
  cases optBs with
  | none =>
    dsimp only [optBoxU8At, optSliceDeallocX]
    rw [ProofLib.memRegion_eight (a + 8#64), sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro l
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right l ?_)
    simp only [beq_self_eq_true, ↓reduceIte, sepConj_emp]
    exact Entails.refl _
  | some bs =>
    dsimp only [optBoxU8At, optSliceDeallocX]
    refine Entails.trans (boxU8At_entails_sliceDeallocX A a ptr bs) ?_
    refine Entails.sepExists_right ptr (Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_)
    refine sepConj_mono_right (sepConj_mono_right ?_)
    apply Entails.pure_left; intro hptr
    have hbeq : (ptr == 0#64) = false := beq_eq_false_iff_ne.mpr hptr
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    exact Entails.refl _

theorem optKyberAt_entails_optSliceDeallocX (A : RustAlloc) (a ptr : BitVec 64)
    (optK : Option KyberPayload) :
    optKyberAt A a ptr optK ⊢
      ∃∗ p : BitVec 64, ∃∗ l : BitVec 64,
        (a ↦₆₄ p) ∗ ((a + 8#64) ↦₆₄ l) ∗ memRegion (a + 16#64) 8 ∗ optSliceDeallocX A p l := by
  cases optK with
  | none =>
    dsimp only [optKyberAt, optSliceDeallocX]
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 8)
          (b' := a + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (a + 8#64), sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro l
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right l ?_)
    simp only [beq_self_eq_true, ↓reduceIte, sepConj_emp]
    exact Entails.refl _
  | some k =>
    dsimp only [optKyberAt, optSliceDeallocX]
    have htail : ((a + 0x10#64) ↦₃₂ k.preKeyId) ∗ memRegion (a + 0x14#64) 4 ⊢ memRegion (a + 16#64) 8 := by
      rw [ProofLib.memRegion_split' (b := a + 16#64) (n := 4) (k := 4)
            (b' := a + 20#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_left
        (IsBlock.entails (IsBlock.pointsTo32 (a + 16#64) k.preKeyId) (IsBlock.memRegion (a + 16#64) 4) fun _ _ => trivial)
    refine Entails.trans (sepConj_mono (boxU8At_entails_sliceDeallocX A a ptr k.ciphertext) htail) ?_
    refine Entails.sepExists_right ptr (Entails.sepExists_right (BitVec.ofNat 64 k.ciphertext.length) ?_)
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right ?_)
    apply Entails.pure_left; intro hptr
    have hbeq : (ptr == 0#64) = false := beq_eq_false_iff_ne.mpr hptr
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem vecU8At_entails_sliceDeallocX (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
      sliceDeallocX A ptr cap := by
  refine Entails.trans (vecU8At_entails_dealloc A a cap ptr bs) ?_
  unfold vecHeader sliceDeallocX
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
  have hbeq : ((cap == 0#64) = true) ↔ cap = 0 := beq_iff_eq
  simp only [hbeq]
  rw [sepConj_assoc, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
  by_cases h0 : cap = 0
  · simp only [h0, ↓reduceIte]; exact Entails.refl _
  · simp only [h0, ↓reduceIte]
    have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun h => h0 (BitVec.eq_of_toNat_eq h))
    exact Entails.pure_right ⟨hpos, hcap_lt⟩ (Entails.refl _)

theorem optU32At_entails_memRegion8 (a : BitVec 64) (o : Option (BitVec 32)) :
    optU32At a o ⊢ memRegion a 8 := by
  cases o with
  | none =>
    unfold optU32At
    rw [ProofLib.memRegion_split' (b := a) (n := 4) (k := 4) (b' := a + 4#64) rfl rfl (by decide)]
    exact sepConj_mono_left
      (IsBlock.entails (IsBlock.pointsTo32 a 0#32) (IsBlock.memRegion a 4) fun _ _ => trivial)
  | some v =>
    unfold optU32At
    rw [ProofLib.memRegion_split' (b := a) (n := 4) (k := 4) (b' := a + 4#64) rfl rfl (by decide)]
    exact sepConj_mono
      (IsBlock.entails (IsBlock.pointsTo32 a 1#32) (IsBlock.memRegion a 4) fun _ _ => trivial)
      (IsBlock.entails (IsBlock.pointsTo32 (a + 4#64) v) (IsBlock.memRegion (a + 4#64) 4) fun _ _ => trivial)

theorem pkBytes_entails_memRegion32 (a : BitVec 64) (pk : PublicKey) :
    (a ↦ₛ pk.bytes.toList) ⊢ memRegion a 32 := by
  have h := ProofLib.pointsToBytes_entails_memRegion a pk.bytes.toList
  have hl : pk.bytes.toList.length = 32 := by simp
  rwa [hl] at h

theorem trailer16_entails_memRegion16 (a : BitVec 64) (u1 u2 : BitVec 32) (b : BitVec 8) :
    (a ↦₃₂ u1) ∗ ((a + 4#64) ↦₃₂ u2) ∗ ((a + 8#64) ↦₈ b) ∗ memRegion (a + 9#64) 7 ⊢
      memRegion a 16 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 4) (k := 12) (b' := a + 4#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 4#64) (n := 4) (k := 8) (b' := a + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 1) (k := 7) (b' := a + 9#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono
    (IsBlock.entails (IsBlock.pointsTo32 a u1) (IsBlock.memRegion a 4) fun _ _ => trivial)
    (sepConj_mono
      (IsBlock.entails (IsBlock.pointsTo32 (a + 4#64) u2) (IsBlock.memRegion (a + 4#64) 4) fun _ _ => trivial)
      (sepConj_mono_left
        (IsBlock.entails (IsBlock.pointsTo8 (a + 8#64) b) (IsBlock.memRegion (a + 8#64) 1) fun _ _ => trivial)))

def pkmPassiveAt (a : BitVec 64) : SepProp :=
  memRegion (a + 16#64) 8 ∗ memRegion (a + 56#64) 32 ∗
    memRegion (a + 104#64) 24 ∗ memRegion (a + 160#64) 88

@[reducible]
def pkmHeadersAt (a pqCap pqPtr ctPtr ctLen mserPtr mserLen
    adPtr adLen serPtr serLen kPtr kLen : BitVec 64) : SepProp :=
  (a ↦₆₄ pqCap) ∗ ((a + 8#64) ↦₆₄ pqPtr) ∗
  ((a + 24#64) ↦₆₄ ctPtr) ∗ ((a + 32#64) ↦₆₄ ctLen) ∗
  ((a + 40#64) ↦₆₄ mserPtr) ∗ ((a + 48#64) ↦₆₄ mserLen) ∗
  ((a + 88#64) ↦₆₄ adPtr) ∗ ((a + 96#64) ↦₆₄ adLen) ∗
  ((a + 128#64) ↦₆₄ serPtr) ∗ ((a + 136#64) ↦₆₄ serLen) ∗
  ((a + 144#64) ↦₆₄ kPtr) ∗ ((a + 152#64) ↦₆₄ kLen) ∗
  pkmPassiveAt a

theorem preKeyMsgAt_entails_deallocX (A : RustAlloc) (g : PreKeyMsgGhost) (a : BitVec 64)
    (m : PreKeySignalMessage) :
    preKeyMsgAt A g a m ⊢
      ∃∗ adPtr : BitVec 64, ∃∗ adLen : BitVec 64, ∃∗ kPtr : BitVec 64, ∃∗ kLen : BitVec 64,
        optSliceDeallocX A kPtr kLen ∗
        sliceDeallocX A g.msg.ctPtr (BitVec.ofNat 64 m.message.ciphertext.length) ∗
        sliceDeallocX A g.msg.pqPtr g.msg.pqCap ∗
        optSliceDeallocX A adPtr adLen ∗
        sliceDeallocX A g.msg.serPtr (BitVec.ofNat 64 m.message.serialized.length) ∗
        sliceDeallocX A g.serPtr (BitVec.ofNat 64 m.serialized.length) ∗
        pkmHeadersAt a g.msg.pqCap g.msg.pqPtr
          g.msg.ctPtr (BitVec.ofNat 64 m.message.ciphertext.length)
          g.msg.serPtr (BitVec.ofNat 64 m.message.serialized.length)
          adPtr adLen
          g.serPtr (BitVec.ofNat 64 m.serialized.length)
          kPtr kLen := by
  unfold preKeyMsgAt signalMessageAt
  rw [sepConj_assoc]
  apply Entails.pure_left; intro _
  have hpq := vecU8At_entails_sliceDeallocX A a g.msg.pqCap g.msg.pqPtr m.message.pqRatchet
  have hct0 := boxU8At_entails_sliceDeallocX A (a + 24#64) g.msg.ctPtr m.message.ciphertext
  have hct : boxU8At A (a + 24#64) g.msg.ctPtr m.message.ciphertext ⊢
      ((a + 24#64) ↦₆₄ g.msg.ctPtr) ∗
      ((a + 32#64) ↦₆₄ BitVec.ofNat 64 m.message.ciphertext.length) ∗
      sliceDeallocX A g.msg.ctPtr (BitVec.ofNat 64 m.message.ciphertext.length) := by
    refine Entails.trans hct0 ?_
    have e : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    rw [e]; exact sepConj_mono_right (sepConj_mono_right (Entails.pure_left fun _ => Entails.refl _))
  have hmser0 := boxU8At_entails_sliceDeallocX A (a + 40#64) g.msg.serPtr m.message.serialized
  have hmser : boxU8At A (a + 40#64) g.msg.serPtr m.message.serialized ⊢
      ((a + 40#64) ↦₆₄ g.msg.serPtr) ∗
      ((a + 48#64) ↦₆₄ BitVec.ofNat 64 m.message.serialized.length) ∗
      sliceDeallocX A g.msg.serPtr (BitVec.ofNat 64 m.message.serialized.length) := by
    refine Entails.trans hmser0 ?_
    have e : a + 40#64 + 8#64 = a + 48#64 := by bv_omega
    rw [e]; exact sepConj_mono_right (sepConj_mono_right (Entails.pure_left fun _ => Entails.refl _))
  have hsrk := pkBytes_entails_memRegion32 (a + 56#64) m.message.senderRatchetKey
  have had := optBoxU8At_entails_optSliceDeallocX A (a + 88#64) g.msg.addrPtr m.message.addresses
  have hmid :
      (((a + 104#64) ↦₃₂ m.message.counter) ∗ ((a + 108#64) ↦₃₂ m.message.previousCounter) ∗
        ((a + 112#64) ↦₈ m.message.messageVersion) ∗ memRegion (a + 113#64) 7) ∗
        optU32At (a + 120#64) m.preKeyId ⊢
      memRegion (a + 104#64) 24 := by
    have ht := trailer16_entails_memRegion16 (a + 104#64)
      m.message.counter m.message.previousCounter m.message.messageVersion
    have e1 : a + 104#64 + 4#64 = a + 108#64 := by bv_omega
    have e2 : a + 104#64 + 8#64 = a + 112#64 := by bv_omega
    have e3 : a + 104#64 + 9#64 = a + 113#64 := by bv_omega
    rw [e1, e2, e3] at ht
    rw [ProofLib.memRegion_split' (b := a + 104#64) (n := 16) (k := 8)
          (b' := a + 120#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono ht (optU32At_entails_memRegion8 (a + 120#64) m.preKeyId)
  have hser0 := boxU8At_entails_sliceDeallocX A (a + 128#64) g.serPtr m.serialized
  have hser : boxU8At A (a + 128#64) g.serPtr m.serialized ⊢
      ((a + 128#64) ↦₆₄ g.serPtr) ∗
      ((a + 136#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
      sliceDeallocX A g.serPtr (BitVec.ofNat 64 m.serialized.length) := by
    refine Entails.trans hser0 ?_
    have e : a + 128#64 + 8#64 = a + 136#64 := by bv_omega
    rw [e]; exact sepConj_mono_right (sepConj_mono_right (Entails.pure_left fun _ => Entails.refl _))
  have hkyb := optKyberAt_entails_optSliceDeallocX A (a + 144#64) g.kyberPtr m.kyberPayload
  have hend :
      memRegion (a + 160#64) 8 ∗ ((a + 168#64) ↦ₛ m.baseKey.bytes.toList) ∗
        ((a + 200#64) ↦ₛ m.identityKey.publicKey.bytes.toList) ∗
        (((a + 232#64) ↦₃₂ m.registrationId) ∗ ((a + 236#64) ↦₃₂ m.signedPreKeyId) ∗
          ((a + 240#64) ↦₈ m.messageVersion) ∗ memRegion (a + 241#64) 7) ⊢
      memRegion (a + 160#64) 88 := by
    have ht := trailer16_entails_memRegion16 (a + 232#64)
      m.registrationId m.signedPreKeyId m.messageVersion
    have e1 : a + 232#64 + 4#64 = a + 236#64 := by bv_omega
    have e2 : a + 232#64 + 8#64 = a + 240#64 := by bv_omega
    have e3 : a + 232#64 + 9#64 = a + 241#64 := by bv_omega
    rw [e1, e2, e3] at ht
    rw [ProofLib.memRegion_split' (b := a + 160#64) (n := 8) (k := 80)
          (b' := a + 168#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 168#64) (n := 32) (k := 48)
          (b' := a + 200#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 200#64) (n := 32) (k := 16)
          (b' := a + 232#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (Entails.refl _)
      (sepConj_mono (pkBytes_entails_memRegion32 (a + 168#64) m.baseKey)
        (sepConj_mono (pkBytes_entails_memRegion32 (a + 200#64) m.identityKey.publicKey) ht))
  have hnorm :
      (vecU8At A a g.msg.pqCap g.msg.pqPtr m.message.pqRatchet ∗
        boxU8At A (a + asm64% smCiphertextOff) g.msg.ctPtr m.message.ciphertext ∗
        boxU8At A (a + asm64% smSerializedOff) g.msg.serPtr m.message.serialized ∗
        ((a + asm64% smSenderRatchetKeyOff) ↦ₛ m.message.senderRatchetKey.bytes.toList) ∗
        optBoxU8At A (a + asm64% smAddressesOff) g.msg.addrPtr m.message.addresses ∗
        ((a + asm64% smCounterOff) ↦₃₂ m.message.counter) ∗
        ((a + asm64% smPreviousCounterOff) ↦₃₂ m.message.previousCounter) ∗
        ((a + asm64% smMessageVersionOff) ↦₈ m.message.messageVersion) ∗
        memRegion (a + asm64% (smMessageVersionOff + 1)) (asm% (signalMessageSize - (smMessageVersionOff + 1)))) ∗
        optU32At (a + 0x78#64) m.preKeyId ∗
        boxU8At A (a + 0x80#64) g.serPtr m.serialized ∗
        optKyberAt A (a + 0x90#64) g.kyberPtr m.kyberPayload ∗
        ((a + 0xa8#64) ↦ₛ m.baseKey.bytes.toList) ∗
        ((a + 0xc8#64) ↦ₛ m.identityKey.publicKey.bytes.toList) ∗
        ((a + 0xe8#64) ↦₃₂ m.registrationId) ∗
        ((a + 0xec#64) ↦₃₂ m.signedPreKeyId) ∗
        ((a + 0xf0#64) ↦₈ m.messageVersion) ∗
        memRegion (a + 0xf1#64) 7 =
      optBoxU8At A (a + 88#64) g.msg.addrPtr m.message.addresses ∗
      optKyberAt A (a + 144#64) g.kyberPtr m.kyberPayload ∗
      (vecU8At A a g.msg.pqCap g.msg.pqPtr m.message.pqRatchet ∗
        boxU8At A (a + 24#64) g.msg.ctPtr m.message.ciphertext ∗
        boxU8At A (a + 40#64) g.msg.serPtr m.message.serialized ∗
        ((a + 56#64) ↦ₛ m.message.senderRatchetKey.bytes.toList) ∗
        ((((a + 104#64) ↦₃₂ m.message.counter) ∗ ((a + 108#64) ↦₃₂ m.message.previousCounter) ∗
          ((a + 112#64) ↦₈ m.message.messageVersion) ∗ memRegion (a + 113#64) 7) ∗
          optU32At (a + 120#64) m.preKeyId) ∗
        boxU8At A (a + 128#64) g.serPtr m.serialized ∗
        (((a + 168#64) ↦ₛ m.baseKey.bytes.toList) ∗
          ((a + 200#64) ↦ₛ m.identityKey.publicKey.bytes.toList) ∗
          (((a + 232#64) ↦₃₂ m.registrationId) ∗ ((a + 236#64) ↦₃₂ m.signedPreKeyId) ∗
            ((a + 240#64) ↦₈ m.messageVersion) ∗ memRegion (a + 241#64) 7))) := by
    ac_rfl
  rw [hnorm]
  refine Entails.trans (sepConj_mono had (sepConj_mono hkyb
    (sepConj_mono hpq (sepConj_mono hct (sepConj_mono hmser
      (sepConj_mono hsrk (sepConj_mono hmid (sepConj_mono_left hser)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro kPtr
  apply Entails.sepExists_elim; intro kLen
  apply Entails.sepExists_elim; intro adPtr
  apply Entails.sepExists_elim; intro adLen
  refine Entails.sepExists_right adPtr (Entails.sepExists_right adLen
    (Entails.sepExists_right kPtr (Entails.sepExists_right kLen ?_)))
  have ea : a + 88#64 + 8#64 = a + 96#64 := by bv_omega
  have ek1 : a + 144#64 + 8#64 = a + 152#64 := by bv_omega
  have ek2 : a + 144#64 + 16#64 = a + 160#64 := by bv_omega
  rw [ea, ek1, ek2]
  have hgroup :
      (((a + 88#64) ↦₆₄ adPtr) ∗ ((a + 96#64) ↦₆₄ adLen) ∗ optSliceDeallocX A adPtr adLen) ∗
        (((a + 144#64) ↦₆₄ kPtr) ∗ ((a + 152#64) ↦₆₄ kLen) ∗ memRegion (a + 160#64) 8 ∗
          optSliceDeallocX A kPtr kLen) ∗
        (((a ↦₆₄ g.msg.pqCap) ∗ ((a + 8#64) ↦₆₄ g.msg.pqPtr) ∗ memRegion (a + 16#64) 8 ∗
            sliceDeallocX A g.msg.pqPtr g.msg.pqCap) ∗
          (((a + 24#64) ↦₆₄ g.msg.ctPtr) ∗
            ((a + 32#64) ↦₆₄ BitVec.ofNat 64 m.message.ciphertext.length) ∗
            sliceDeallocX A g.msg.ctPtr (BitVec.ofNat 64 m.message.ciphertext.length)) ∗
          (((a + 40#64) ↦₆₄ g.msg.serPtr) ∗
            ((a + 48#64) ↦₆₄ BitVec.ofNat 64 m.message.serialized.length) ∗
            sliceDeallocX A g.msg.serPtr (BitVec.ofNat 64 m.message.serialized.length)) ∗
          memRegion (a + 56#64) 32 ∗
          memRegion (a + 104#64) 24 ∗
          (((a + 128#64) ↦₆₄ g.serPtr) ∗
            ((a + 136#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
            sliceDeallocX A g.serPtr (BitVec.ofNat 64 m.serialized.length)) ∗
          (((a + 168#64) ↦ₛ m.baseKey.bytes.toList) ∗
            ((a + 200#64) ↦ₛ m.identityKey.publicKey.bytes.toList) ∗
            (((a + 232#64) ↦₃₂ m.registrationId) ∗ ((a + 236#64) ↦₃₂ m.signedPreKeyId) ∗
              ((a + 240#64) ↦₈ m.messageVersion) ∗ memRegion (a + 241#64) 7))) =
      (memRegion (a + 160#64) 8 ∗ ((a + 168#64) ↦ₛ m.baseKey.bytes.toList) ∗
        ((a + 200#64) ↦ₛ m.identityKey.publicKey.bytes.toList) ∗
        (((a + 232#64) ↦₃₂ m.registrationId) ∗ ((a + 236#64) ↦₃₂ m.signedPreKeyId) ∗
          ((a + 240#64) ↦₈ m.messageVersion) ∗ memRegion (a + 241#64) 7)) ∗
      (optSliceDeallocX A kPtr kLen ∗
        sliceDeallocX A g.msg.ctPtr (BitVec.ofNat 64 m.message.ciphertext.length) ∗
        sliceDeallocX A g.msg.pqPtr g.msg.pqCap ∗
        optSliceDeallocX A adPtr adLen ∗
        sliceDeallocX A g.msg.serPtr (BitVec.ofNat 64 m.message.serialized.length) ∗
        sliceDeallocX A g.serPtr (BitVec.ofNat 64 m.serialized.length) ∗
        (a ↦₆₄ g.msg.pqCap) ∗ ((a + 8#64) ↦₆₄ g.msg.pqPtr) ∗
        ((a + 24#64) ↦₆₄ g.msg.ctPtr) ∗
        ((a + 32#64) ↦₆₄ BitVec.ofNat 64 m.message.ciphertext.length) ∗
        ((a + 40#64) ↦₆₄ g.msg.serPtr) ∗
        ((a + 48#64) ↦₆₄ BitVec.ofNat 64 m.message.serialized.length) ∗
        ((a + 88#64) ↦₆₄ adPtr) ∗ ((a + 96#64) ↦₆₄ adLen) ∗
        ((a + 128#64) ↦₆₄ g.serPtr) ∗
        ((a + 136#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
        ((a + 144#64) ↦₆₄ kPtr) ∗ ((a + 152#64) ↦₆₄ kLen) ∗
        memRegion (a + 16#64) 8 ∗ memRegion (a + 56#64) 32 ∗ memRegion (a + 104#64) 24) := by
    ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_left hend) ?_
  unfold pkmHeadersAt pkmPassiveAt
  exact Entails.of_eq (by ac_rfl)

theorem pkmHeadersAt_entails_memRegion_248
    (a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen : BitVec 64) :
    pkmHeadersAt a pqCap pqPtr ctPtr ctLen mserPtr mserLen
      adPtr adLen serPtr serLen kPtr kLen ⊢ memRegion a 248 := by
  unfold pkmHeadersAt pkmPassiveAt
  have pair16 : ∀ (b x y : BitVec 64), (b ↦₆₄ x) ∗ ((b + 8#64) ↦₆₄ y) ⊢ memRegion b 16 := by
    intro b x y
    rw [ProofLib.memRegion_split' (b := b) (n := 8) (k := 8) (b' := b + 8#64) rfl rfl (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion b x) (pointsTo64_entails_memRegion (b + 8#64) y)
  have h1 := DropGlueFacts.header_cells_entails_memRegion_24 a pqCap pqPtr
  have h2 := pair16 (a + 24#64) ctPtr ctLen
  have h3 := pair16 (a + 40#64) mserPtr mserLen
  have h4 := pair16 (a + 88#64) adPtr adLen
  have h5 := pair16 (a + 128#64) serPtr serLen
  have h6 := pair16 (a + 144#64) kPtr kLen
  have e2 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have e3 : a + 40#64 + 8#64 = a + 48#64 := by bv_omega
  have e4 : a + 88#64 + 8#64 = a + 96#64 := by bv_omega
  have e5 : a + 128#64 + 8#64 = a + 136#64 := by bv_omega
  have e6 : a + 144#64 + 8#64 = a + 152#64 := by bv_omega
  rw [e2] at h2; rw [e3] at h3; rw [e4] at h4; rw [e5] at h5; rw [e6] at h6
  have hord :
      (a ↦₆₄ pqCap) ∗ ((a + 8#64) ↦₆₄ pqPtr) ∗
        ((a + 24#64) ↦₆₄ ctPtr) ∗ ((a + 32#64) ↦₆₄ ctLen) ∗
        ((a + 40#64) ↦₆₄ mserPtr) ∗ ((a + 48#64) ↦₆₄ mserLen) ∗
        ((a + 88#64) ↦₆₄ adPtr) ∗ ((a + 96#64) ↦₆₄ adLen) ∗
        ((a + 128#64) ↦₆₄ serPtr) ∗ ((a + 136#64) ↦₆₄ serLen) ∗
        ((a + 144#64) ↦₆₄ kPtr) ∗ ((a + 152#64) ↦₆₄ kLen) ∗
        (memRegion (a + 16#64) 8 ∗ memRegion (a + 56#64) 32 ∗
          memRegion (a + 104#64) 24 ∗ memRegion (a + 160#64) 88) =
      ((a ↦₆₄ pqCap) ∗ ((a + 8#64) ↦₆₄ pqPtr) ∗ memRegion (a + 16#64) 8) ∗
      (((a + 24#64) ↦₆₄ ctPtr) ∗ ((a + 32#64) ↦₆₄ ctLen)) ∗
      (((a + 40#64) ↦₆₄ mserPtr) ∗ ((a + 48#64) ↦₆₄ mserLen)) ∗
      memRegion (a + 56#64) 32 ∗
      (((a + 88#64) ↦₆₄ adPtr) ∗ ((a + 96#64) ↦₆₄ adLen)) ∗
      memRegion (a + 104#64) 24 ∗
      (((a + 128#64) ↦₆₄ serPtr) ∗ ((a + 136#64) ↦₆₄ serLen)) ∗
      (((a + 144#64) ↦₆₄ kPtr) ∗ ((a + 152#64) ↦₆₄ kLen)) ∗
      memRegion (a + 160#64) 88 := by
    ac_rfl
  rw [hord]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3
    (sepConj_mono (Entails.refl _) (sepConj_mono h4 (sepConj_mono (Entails.refl _)
      (sepConj_mono h5 (sepConj_mono_left h6)))))))) ?_
  rw [ProofLib.memRegion_split' (b := a) (n := 24) (k := 224) (b' := a + 24#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 16) (k := 208) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 16) (k := 192) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 32) (k := 160) (b' := a + 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 88#64) (n := 16) (k := 144) (b' := a + 104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 104#64) (n := 24) (k := 120) (b' := a + 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 128#64) (n := 16) (k := 104) (b' := a + 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 144#64) (n := 16) (k := 88) (b' := a + 160#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

/-! ## Epilogue heap and stack entailments -/

private theorem pkm_empty_epilogue_weaken
    (a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen : BitVec 64)
    (Pool : SepProp) (sp fp lr x19 c3 : BitVec 64) :
    pkmHeadersAt a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen ∗
      Pool ∗ stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ c3) ⊢
    memRegion a 248 ∗ Pool ∗ stackAt sp (32 + extHookStack) := by
  have hh := pkmHeadersAt_entails_memRegion_248
    a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen
  have hs := stack_restore_32X sp fp lr x19 c3
  exact sepConj_mono hh (sepConj_mono_right hs)

private theorem pkm_tail_dealloc_pre_weaken
    (a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen : BitVec 64)
    (Live Pool : SepProp) (sp fp lr x19 c3 : BitVec 64) :
    pkmHeadersAt a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen ∗
      Live ∗ Pool ∗ stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ c3) ⊢
    Pool ∗ Live ∗ stackAt sp extHookStack ∗
      (memRegion a 248 ∗ memRegion (sp - 16416#64) 32) := by
  have hh := pkmHeadersAt_entails_memRegion_248
    a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen
  have hs := cells4_entails_stack_bottomX sp fp lr x19 c3
  have hgroup :
      pkmHeadersAt a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen ∗
        Live ∗ Pool ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ c3) =
      pkmHeadersAt a pqCap pqPtr ctPtr ctLen mserPtr mserLen adPtr adLen serPtr serLen kPtr kLen ∗
        (Live ∗ Pool ∗
          (stackAt (sp - 32#64) extHookStack ∗
            ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
            ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ c3))) := by
    ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono hh (sepConj_mono_right (sepConj_mono_right hs))) ?_
  exact Entails.of_eq (by ac_rfl)

private theorem pkm_tail_dealloc_post_weaken (a : BitVec 64) (Pool : SepProp) (sp : BitVec 64) :
    Pool ∗ stackAt sp extHookStack ∗ (memRegion a 248 ∗ memRegion (sp - 16416#64) 32) ⊢
      memRegion a 248 ∗ Pool ∗ stackAt sp (32 + extHookStack) := by
  rw [stackAt_pkm_split sp, ← tail_stack_32_from_bottomX sp]
  exact Entails.of_eq (by ac_rfl)

/-! ## Callee-saved register preservation -/

@[reducible]
private def Saved32Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x20 = s0.readReg64 .x20 ∧
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem seq_cleanX {prog : Program} {img : Obj.Image} {mid target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post := by
  refine ProofLib.SepWP.of_sepWP_inv hfrozen hsym (SepWP.mono h1 ?_)
  intro sm Pm hpc hrun ⟨hent, hQ⟩ hfrozen_m hsym_m
  exact SepWP.weaken_pre hent (h2 sm hpc hrun hfrozen_m hsym_m hQ)

private theorem align_to_post {prog : Program} {mid : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (heq : P = P_mid)
    (hwp : SepWP prog mid s P_mid (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) :=
  heq ▸ hwp

/-! ## Exact-stack contract (`32 + extHookStack`) -/

def dropPreKeyMsgExactSpec (A : RustAlloc) :
    Spec (BitVec 64 × PreKeyMsgGhost × PreKeySignalMessage) where
  pre := fun (a, g, m) s =>
    ⌜s.readReg64 .x0 = a⌝ ∗ preKeyMsgAt A g a m ∗ A.pool ∗ stackAt s.sp (32 + extHookStack)
  post := fun (a, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion a 248 ∗ A.pool ∗ stackAt s0.sp (32 + extHookStack)

set_option maxHeartbeats 1600000 in
theorem dropPreKeyMsgExact_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>")
      ((dropPreKeyMsgExactSpec A).inImage img) := by
  simp only [Spec.inImage, dropPreKeyMsgExactSpec]
  have hdealloc := hA.dealloc_ok_at
    "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>"
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>"))
    (by rw [(ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>")];
        simp only [arm64_norm])
  simp only [Spec.inImage, rustDeallocExternSpecWithStack, LayoutOk] at hdealloc
  code_fetches libsignalSessionCode pkmDec img.base
    (Rust.withPanics ext)
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>")
    (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>")) 164
  dsimp only [tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>" = entry
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨a, g, m⟩
  dsimp only at *
  subst h
  set a0 := s0.readReg64 (Reg.gpr 0#5)
  set ctLen := BitVec.ofNat 64 m.message.ciphertext.length
  set mserLen := BitVec.ofNat 64 m.message.serialized.length
  set serLen := BitVec.ofNat 64 m.serialized.length
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_pkm_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i c0 c1 c2 c3
  refine SepWP.weaken_pre (sepConj_mono_left (preKeyMsgAt_entails_deallocX A g a0 m)) ?_
  wp_pull_exists
  rename_i adPtr adLen kPtr kLen
  let Hdrs : SepProp :=
    pkmHeadersAt a0 g.msg.pqCap g.msg.pqPtr g.msg.ctPtr ctLen g.msg.serPtr mserLen
      adPtr adLen g.serPtr serLen kPtr kLen
  let SavedSlots : SepProp :=
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ c3)
  refine seq_cleanX (mid := entry + bv% (16))
    (P_mid := optSliceDeallocX A kPtr kLen ∗
      sliceDeallocX A g.msg.ctPtr ctLen ∗
      sliceDeallocX A g.msg.pqPtr g.msg.pqCap ∗
      optSliceDeallocX A adPtr adLen ∗
      sliceDeallocX A g.msg.serPtr mserLen ∗
      sliceDeallocX A g.serPtr serLen ∗
      Hdrs ∗ A.pool ∗ stackAt (s0.sp - 32#64) extHookStack ∗ SavedSlots)
    (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) ∧
      sm.readReg64 .x0 = a0 ∧ sm.readReg64 .x19 = a0)
    h_2 h_1 ?_ ?_
  · wp_steps
    refine align_to_post (by dsimp only [Hdrs, SavedSlots, pkmHeadersAt]; ac_rfl) ?_
    wp_done
  · intro s0p hpc0 hrun0 hfrozen0 hsym0
      ⟨⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩, hx0_0, hx19_0⟩
    refine seq_cleanX (mid := entry + bv% (40))
      (P_mid := sliceDeallocX A g.msg.ctPtr ctLen ∗
        sliceDeallocX A g.msg.pqPtr g.msg.pqCap ∗
        optSliceDeallocX A adPtr adLen ∗
        sliceDeallocX A g.msg.serPtr mserLen ∗
        sliceDeallocX A g.serPtr serLen ∗
        Hdrs ∗ A.pool ∗ stackAt (s0.sp - 32#64) extHookStack ∗ SavedSlots)
      (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a0)
      hfrozen0 hsym0 ?_ ?_
    · dsimp only [Hdrs, pkmHeadersAt]
      rw [optSliceDeallocX_eq]
      by_cases hk1 : (kPtr == 0#64) = true
      · simp only [hk1, ↓reduceIte, emp_sepConj]
        wp_steps
        wp_done
      · simp only [hk1, Bool.false_eq_true, ↓reduceIte]
        rw [sliceDeallocX_eq]
        by_cases hk2 : (kLen == 0#64) = true
        · simp only [hk2, ↓reduceIte, emp_sepConj]
          wp_steps
          wp_done
        · simp only [hk2, Bool.false_eq_true, ↓reduceIte]
          rw [sepConj_assoc]
          refine SepWP.pure_elim ?_
          rintro ⟨hpos, hlt⟩
          wp_steps
          wp_call hdealloc (kPtr, kLen.toNat, 1)
          refine align_to_post (by rw [hsp_0]; ac_rfl) ?_
          wp_done
    · intro s1 hpc1 hrun1 hfrozen1 hsym1
        ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
      refine seq_cleanX (mid := entry + bv% (60))
        (P_mid := sliceDeallocX A g.msg.pqPtr g.msg.pqCap ∗
          optSliceDeallocX A adPtr adLen ∗
          sliceDeallocX A g.msg.serPtr mserLen ∗
          sliceDeallocX A g.serPtr serLen ∗
          Hdrs ∗ A.pool ∗ stackAt (s0.sp - 32#64) extHookStack ∗ SavedSlots)
        (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a0)
        hfrozen1 hsym1 ?_ ?_
      · dsimp only [Hdrs, pkmHeadersAt]
        rw [sliceDeallocX_eq]
        by_cases hct : (ctLen == 0#64) = true
        · simp only [hct, ↓reduceIte, emp_sepConj]
          wp_steps
          wp_done
        · simp only [hct, Bool.false_eq_true, ↓reduceIte]
          rw [sepConj_assoc]
          refine SepWP.pure_elim ?_
          rintro ⟨hpos, hlt⟩
          wp_steps
          wp_call hdealloc (g.msg.ctPtr, ctLen.toNat, 1)
          refine align_to_post (by rw [hsp_1]; ac_rfl) ?_
          wp_done
      · intro s2 hpc2 hrun2 hfrozen2 hsym2
          ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
        refine seq_cleanX (mid := entry + bv% (80))
          (P_mid := optSliceDeallocX A adPtr adLen ∗
            sliceDeallocX A g.msg.serPtr mserLen ∗
            sliceDeallocX A g.serPtr serLen ∗
            Hdrs ∗ A.pool ∗ stackAt (s0.sp - 32#64) extHookStack ∗ SavedSlots)
          (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a0)
          hfrozen2 hsym2 ?_ ?_
        · dsimp only [Hdrs, pkmHeadersAt]
          rw [sliceDeallocX_eq]
          by_cases hpq : (g.msg.pqCap == 0#64) = true
          · simp only [hpq, ↓reduceIte, emp_sepConj]
            wp_steps
            wp_done
          · simp only [hpq, Bool.false_eq_true, ↓reduceIte]
            rw [sepConj_assoc]
            refine SepWP.pure_elim ?_
            rintro ⟨hpos, hlt⟩
            wp_steps
            wp_call hdealloc (g.msg.pqPtr, g.msg.pqCap.toNat, 1)
            refine align_to_post (by rw [hsp_2]; ac_rfl) ?_
            wp_done
        · intro s3 hpc3 hrun3 hfrozen3 hsym3
            ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
          refine seq_cleanX (mid := entry + bv% (104))
            (P_mid := sliceDeallocX A g.msg.serPtr mserLen ∗
              sliceDeallocX A g.serPtr serLen ∗
              Hdrs ∗ A.pool ∗ stackAt (s0.sp - 32#64) extHookStack ∗ SavedSlots)
            (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a0)
            hfrozen3 hsym3 ?_ ?_
          · dsimp only [Hdrs, pkmHeadersAt]
            rw [optSliceDeallocX_eq]
            by_cases had1 : (adPtr == 0#64) = true
            · simp only [had1, ↓reduceIte, emp_sepConj]
              wp_steps
              wp_done
            · simp only [had1, Bool.false_eq_true, ↓reduceIte]
              rw [sliceDeallocX_eq]
              by_cases had2 : (adLen == 0#64) = true
              · simp only [had2, ↓reduceIte, emp_sepConj]
                wp_steps
                wp_done
              · simp only [had2, Bool.false_eq_true, ↓reduceIte]
                rw [sepConj_assoc]
                refine SepWP.pure_elim ?_
                rintro ⟨hpos, hlt⟩
                wp_steps
                wp_call hdealloc (adPtr, adLen.toNat, 1)
                refine align_to_post (by rw [hsp_3]; ac_rfl) ?_
                wp_done
          · intro s4 hpc4 hrun4 hfrozen4 hsym4
              ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
            refine seq_cleanX (mid := entry + bv% (124))
              (P_mid := sliceDeallocX A g.serPtr serLen ∗
                Hdrs ∗ A.pool ∗ stackAt (s0.sp - 32#64) extHookStack ∗ SavedSlots)
              (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a0)
              hfrozen4 hsym4 ?_ ?_
            · dsimp only [Hdrs, pkmHeadersAt]
              rw [sliceDeallocX_eq]
              by_cases hmser : (mserLen == 0#64) = true
              · simp only [hmser, ↓reduceIte, emp_sepConj]
                wp_steps
                wp_done
              · simp only [hmser, Bool.false_eq_true, ↓reduceIte]
                rw [sepConj_assoc]
                refine SepWP.pure_elim ?_
                rintro ⟨hpos, hlt⟩
                wp_steps
                wp_call hdealloc (g.msg.serPtr, mserLen.toNat, 1)
                refine align_to_post (by rw [hsp_4]; ac_rfl) ?_
                wp_done
            · intro s5 hpc5 hrun5 hfrozen5 hsym5
                ⟨⟨hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
              dsimp only [Hdrs, SavedSlots, pkmHeadersAt]
              rw [sliceDeallocX_eq]
              by_cases hser : (serLen == 0#64) = true
              · simp only [hser, ↓reduceIte, emp_sepConj]
                wp_steps
                refine SepWP.weaken_pre
                  (pkm_empty_epilogue_weaken a0 g.msg.pqCap g.msg.pqPtr g.msg.ctPtr ctLen
                    g.msg.serPtr mserLen adPtr adLen g.serPtr serLen kPtr kLen
                    A.pool s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) c3) ?_
                wp_done
              · simp only [hser, Bool.false_eq_true, ↓reduceIte]
                rw [sepConj_assoc]
                refine SepWP.pure_elim ?_
                rintro ⟨hpos, hlt⟩
                wp_steps
                have hpre6 := pkm_tail_dealloc_pre_weaken a0 g.msg.pqCap g.msg.pqPtr g.msg.ctPtr ctLen
                  g.msg.serPtr mserLen adPtr adLen g.serPtr serLen kPtr kLen
                  (A.live g.serPtr serLen.toNat 1 ∗ memRegion g.serPtr serLen.toNat) A.pool
                  s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) c3
                refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by dsimp only [pkmHeadersAt]; ac_rfl)) hpre6) ?_
                wp_call hdealloc (g.serPtr, serLen.toNat, 1)
                refine SepWP.weaken_pre (pkm_tail_dealloc_post_weaken a0 A.pool s0.sp) ?_
                wp_done

end CryptoVerification.SignalSession.Cli.RunProofs.DropPreKeyMsgHelpers
