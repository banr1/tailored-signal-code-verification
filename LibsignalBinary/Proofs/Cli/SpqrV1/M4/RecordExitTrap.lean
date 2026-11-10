/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.FetchTail
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# CLI `SegExit` under `AllocContracts` (for `trTrapProgAt` / `cliExterns`)

Generalizes `CryptoVerification.Cli.LibsignalTripleRatchet.Record.segExit_ok_ext` from
`Stage2Contracts` to `AllocContracts img.base A ext` so it applies directly on
`trTrapProgAt img.base C abs` (which omits `rngFillHook`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.Record

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `SatEntails` and `.rodata` Jump Table (28 B) -/

private def SatEntails (P Q : SepProp) : Prop :=
  ∀ (m : Memory) (R : SepProp), (m ⊨ P ∗ R) → (m ⊨ Q ∗ R)

private theorem SatEntails.refl (P : SepProp) : SatEntails P P :=
  fun _ _ hm => hm

private theorem SatEntails.of_eq {P Q : SepProp} (h : P = Q) : SatEntails P Q :=
  h ▸ SatEntails.refl P

private theorem SatEntails.of_entails {P Q : SepProp} (h : P ⊢ Q) : SatEntails P Q :=
  fun _ _ hm => Satisfies.mono (sepConj_mono_left h) hm

private theorem SatEntails.trans {P Q S : SepProp}
    (h1 : SatEntails P Q) (h2 : SatEntails Q S) : SatEntails P S :=
  fun m R hm => h2 m R (h1 m R hm)

private theorem SatEntails.drop_left (P Q : SepProp) : SatEntails (P ∗ Q) Q := by
  intro m R hm
  rw [sepConj_assoc] at hm
  exact Satisfies.of_sep_right hm

private theorem SatEntails.drop_right (P Q : SepProp) : SatEntails (P ∗ Q) P := by
  intro m R hm
  rw [sepConj_comm P Q, sepConj_assoc] at hm
  exact Satisfies.of_sep_right hm

private theorem SatEntails.sepConj_mono {P₁ P₂ Q₁ Q₂ : SepProp}
    (h1 : SatEntails P₁ P₂) (h2 : SatEntails Q₁ Q₂) :
    SatEntails (P₁ ∗ Q₁) (P₂ ∗ Q₂) := by
  intro m R hm
  rw [sepConj_assoc] at hm
  have hm1 := h1 m (Q₁ ∗ R) hm
  rw [← sepConj_assoc, sepConj_comm P₂ Q₁, sepConj_assoc] at hm1
  have hm2 := h2 m (P₂ ∗ R) hm1
  rw [← sepConj_assoc, sepConj_comm Q₂ P₂] at hm2
  exact hm2

private theorem SatEntails.sepConj_mono_left {P₁ P₂ : SepProp}
    (h : SatEntails P₁ P₂) {Q : SepProp} : SatEntails (P₁ ∗ Q) (P₂ ∗ Q) :=
  SatEntails.sepConj_mono h (SatEntails.refl Q)

private theorem SatEntails.sepConj_mono_right {P Q₁ Q₂ : SepProp}
    (h : SatEntails Q₁ Q₂) : SatEntails (P ∗ Q₁) (P ∗ Q₂) :=
  SatEntails.sepConj_mono (SatEntails.refl P) h

private theorem SatEntails.sepExists_elim {α : Type} {P : α → SepProp} {Q : SepProp}
    (h : ∀ x, SatEntails (P x) Q) : SatEntails (∃∗ x, P x) Q := by
  intro m R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x m R hx

private theorem SatEntails.sepExists_right {α : Type} {P : SepProp} {Q : α → SepProp}
    (x : α) (h : SatEntails P (Q x)) : SatEntails P (∃∗ y, Q y) :=
  SatEntails.trans h (SatEntails.of_entails (Entails.sepExists_right x (Entails.refl _)))

private theorem SepWP.weaken_pre_sat {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (himp : SatEntails P P')
    (h : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  exact h R (himp s.mem R hm)

private theorem SepWP.false_elim {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  have heq : (P ∗ ⌜False⌝ ∗ Q) ∗ R = ⌜False⌝ ∗ (P ∗ Q ∗ R) := by ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact False.elim hm.1

private noncomputable def exitJumpTable : List (BitVec 8) :=
  (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 43

private theorem rodata_exitJumpTable_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168))) ↦ᵣ exitJumpTable) ∗ P :=
  ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168))) (secLen := 43) (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP

private theorem exitJumpTable_byte (base : BitVec 64) (i : Nat) (off : BitVec 64) (b : BitVec 8)
    (hoff : bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168)) + BitVec.ofNat 64 (15 + i) = off)
    (heq : exitJumpTable = exitJumpTable.take (15 + i) ++ (b :: exitJumpTable.drop (15 + i + 1)))
    (hlen : (exitJumpTable.take (15 + i)).length = 15 + i) :
    SatEntails ((base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168))) ↦ᵣ exitJumpTable) ((base + off) ↦₈ᵣ b) := by
  have h : ((base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168))) ↦ᵣ exitJumpTable) =
      ((base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168))) ↦ᵣ exitJumpTable.take (15 + i)) ∗
        ((((base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168))) + BitVec.ofNat 64 (15 + i)) ↦₈ᵣ b) ∗
         (((base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168))) + BitVec.ofNat 64 (15 + i) + 1#64) ↦ᵣ exitJumpTable.drop (15 + i + 1))) := by
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen]
  rw [h, BitVec.add_assoc base (bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168))) (BitVec.ofNat 64 (15 + i)), hoff]
  exact SatEntails.trans (SatEntails.drop_left _ _) (SatEntails.drop_right _ _)

private theorem adrp_exitJumpTable_eq_local {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64) (he : entry = base + bv% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) :
    ((entry + bv% (7840)) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 15) - page% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7840)) = base + bv% (page% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 15)) := by
  subst he
  rw [BitVec.add_assoc, adrp_page_of_aligned hb, BitVec.add_assoc]
  rfl

/-! ## 2. `RecErr` / `speAt` Weakening Helpers -/

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

private theorem spe_word8_40_entails_48 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ⊢ memRegion a 48 := by
  rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split a 8 40 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a w)

private theorem spe_u64_at_8_entails_40 (a : BitVec 64) (v : BitVec 64) :
    ((a + 8#64) ↦₆₄ v) ∗ memRegion (a + 16#64) 32 ⊢ memRegion (a + 8#64) 40 := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 := by
    rw [show (40 : Nat) = 8 + 32 from rfl, memRegion_split (a + 8#64) 8 32 (by decide),
        show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (a + 8#64) v)

private theorem spe_u32_at_8_entails_40 (a : BitVec 64) (v : BitVec 32) :
    ((a + 8#64) ↦₃₂ v) ∗ memRegion (a + 12#64) 36 ⊢ memRegion (a + 8#64) 40 := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 4 ∗ memRegion (a + 12#64) 36 := by
    rw [show (40 : Nat) = 4 + 36 from rfl, memRegion_split (a + 8#64) 4 36 (by decide),
        show a + 8#64 + 4#64 = a + 12#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left
    (IsBlock.entails (IsBlock.pointsTo32 (a + 8#64) v) (IsBlock.memRegion (a + 8#64) 4) fun _ _ => trivial)

private theorem spe_u8_at_8_entails_40 (a : BitVec 64) (v : BitVec 8) :
    ((a + 8#64) ↦₈ v) ∗ memRegion (a + 9#64) 39 ⊢ memRegion (a + 8#64) 40 := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 1 ∗ memRegion (a + 9#64) 39 := by
    rw [show (40 : Nat) = 1 + 39 from rfl, memRegion_split (a + 8#64) 1 39 (by decide),
        show a + 8#64 + 1#64 = a + 9#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left
    (IsBlock.entails (IsBlock.pointsTo8 (a + 8#64) v) (IsBlock.memRegion (a + 8#64) 1) fun _ _ => trivial)

private theorem spe_u8_at_32_entails_16 (a : BitVec 64) (v : BitVec 8) :
    ((a + 32#64) ↦₈ v) ∗ memRegion (a + 33#64) 15 ⊢ memRegion (a + 32#64) 16 := by
  have h : memRegion (a + 32#64) 16 = memRegion (a + 32#64) 1 ∗ memRegion (a + 33#64) 15 := by
    rw [show (16 : Nat) = 1 + 15 from rfl, memRegion_split (a + 32#64) 1 15 (by decide),
        show a + 32#64 + 1#64 = a + 33#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left
    (IsBlock.entails (IsBlock.pointsTo8 (a + 32#64) v) (IsBlock.memRegion (a + 32#64) 1) fun _ _ => trivial)

private theorem spe_u32x2_at_8_entails_40 (a : BitVec 64) (v1 v2 : BitVec 32) :
    ((a + 8#64) ↦₃₂ v1) ∗ ((a + 12#64) ↦₃₂ v2) ∗ memRegion (a + 16#64) 32 ⊢
      memRegion (a + 8#64) 40 := by
  have h1 : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 4 ∗ memRegion (a + 12#64) 36 := by
    rw [show (40 : Nat) = 4 + 36 from rfl, memRegion_split (a + 8#64) 4 36 (by decide),
        show a + 8#64 + 4#64 = a + 12#64 by bv_omega]
  have h2 : memRegion (a + 12#64) 36 = memRegion (a + 12#64) 4 ∗ memRegion (a + 16#64) 32 := by
    rw [show (36 : Nat) = 4 + 32 from rfl, memRegion_split (a + 12#64) 4 32 (by decide),
        show a + 12#64 + 4#64 = a + 16#64 by bv_omega]
  rw [h1, h2]
  exact sepConj_mono
    (IsBlock.entails (IsBlock.pointsTo32 (a + 8#64) v1) (IsBlock.memRegion (a + 8#64) 4) fun _ _ => trivial)
    (sepConj_mono_left
      (IsBlock.entails (IsBlock.pointsTo32 (a + 12#64) v2) (IsBlock.memRegion (a + 12#64) 4) fun _ _ => trivial))

private theorem spe_strRef_at_8_entails_40 (a : BitVec 64) (lit : List (BitVec 8)) :
    SatEntails (strRefAt (a + 8#64) lit ∗ memRegion (a + 24#64) 24) (memRegion (a + 8#64) 40) := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 16 ∗ memRegion (a + 24#64) 24 := by
    rw [show (40 : Nat) = 16 + 24 from rfl, memRegion_split (a + 8#64) 16 24 (by decide),
        show a + 8#64 + 16#64 = a + 24#64 by bv_omega]
  rw [h]
  exact SatEntails.sepConj_mono_left (strRefAt_entails_memRegion16 (a + 8#64) lit)

private theorem iscmk_entails_40 (A : RustAlloc) (a : BitVec 64) :
    SatEntails (recErrAt A a .iscmk) ((a ↦₆₄ speWord 20) ∗ memRegion (a + 8#64) 40) := by
  simp only [recErrAt, Proofs.libsignal.SR.DecX.iscmkErrAt, Proofs.libsignal.SR.DecX.iscmkBodyAt]
  rw [show a + 8#64 + 16#64 = a + 24#64 by bv_omega]
  exact SatEntails.sepConj_mono_right (spe_strRef_at_8_entails_40 _ _)

private theorem vecU8At_entails_dealloc (A : RustAlloc) (a : BitVec 64) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
      (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  simp only [vecU8At, vecHeader, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion (a + 16#64) _)) ?_
  refine sepConj_mono_right ?_
  apply Entails.pure_left
  rintro ⟨hlen, hcap_lt, _⟩
  by_cases hcap : cap = 0#64
  · subst hcap
    simp only [beq_self_eq_true, ↓reduceIte]
    exact Entails.refl _
  · have hcap0 : ¬ cap = 0 := hcap
    have hbeq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    simp only [hcap0, hbeq, Bool.false_eq_true, ↓reduceIte]
    refine sepConj_mono_right ?_
    have hsplit : memRegion ptr cap.toNat =
        memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
      have heq : cap.toNat = bs.length + (cap.toNat - bs.length) := by omega
      conv_lhs => rw [heq]
      exact memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)
    rw [hsplit]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

private theorem vecU8_at_8_expose (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (a + 8#64) bs ∗ memRegion (a + 32#64) 16 ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  refine Entails.trans (sepConj_mono_left (vecU8At_entails_dealloc A (a + 8#64) cap ptr bs)) ?_
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have h24 : a + 8#64 + 16#64 = a + 24#64 := by bv_omega
  have hm : memRegion (a + 24#64) 24 = memRegion (a + 24#64) 8 ∗ memRegion (a + 32#64) 16 := by
    rw [show (24 : Nat) = 8 + 16 from rfl, memRegion_split (a + 24#64) 8 16 (by decide),
        show a + 24#64 + 8#64 = a + 32#64 by bv_omega]
  rw [h16, h24, hm]
  exact Entails.of_eq (by ac_rfl)

private theorem spe_str_words_entails_48 (a w cap ptr : BitVec 64) :
    (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ⊢
      memRegion a 48 := by
  have h1 : memRegion a 48 = memRegion a 8 ∗ memRegion (a + 8#64) 40 := by
    rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split a 8 40 (by decide)]
  have h2 : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 := by
    rw [show (40 : Nat) = 8 + 32 from rfl, memRegion_split (a + 8#64) 8 32 (by decide),
        show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  have h3 : memRegion (a + 16#64) 32 = memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 24 := by
    rw [show (32 : Nat) = 8 + 24 from rfl, memRegion_split (a + 16#64) 8 24 (by decide),
        show a + 16#64 + 8#64 = a + 24#64 by bv_omega]
  rw [h1, h2, h3]
  exact sepConj_mono (pointsTo64_entails_memRegion a w)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) cap)
      (sepConj_mono_left (pointsTo64_entails_memRegion (a + 16#64) ptr)))

private theorem spe_str_after_weaken (a w cap ptr : BitVec 64) (ro rest : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ rest)
      (memRegion a 48 ∗ rest) := by
  have hro : SatEntails (ro ∗ rest) rest := SatEntails.drop_left ro rest
  have ha := SatEntails.of_entails (spe_str_words_entails_48 a w cap ptr)
  have hreord :
      (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ rest =
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24) ∗
        (ro ∗ rest) := by ac_rfl
  rw [hreord]
  exact SatEntails.sepConj_mono ha hro

private theorem spe_noop_after_weaken (a w : BitVec 64) (ro rest : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro ∗ rest)
      (memRegion a 48 ∗ rest) := by
  have hro : SatEntails (ro ∗ rest) rest := SatEntails.drop_left ro rest
  have ha := SatEntails.of_entails (spe_word8_40_entails_48 a w)
  have hreord :
      (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro ∗ rest =
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40) ∗ (ro ∗ rest) := by ac_rfl
  rw [hreord]
  exact SatEntails.sepConj_mono ha hro

private theorem speAt_invalidState_expose (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) :
    SatEntails (speAt A fnName a .invalidState)
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  simp only [speAt]
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails.sepExists_elim; intro bs
  refine SatEntails.trans
    (SatEntails.sepConj_mono_right (SatEntails.sepConj_mono_right (strRefAt_entails_memRegion16 (a + 32#64) fnName))) ?_
  apply SatEntails.of_entails
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_expose A a bs)) ?_
  simp only [sepExists_sepConj_right]
  exact Entails.refl _

private theorem invalidMessageStrAt_entails_vecU8 (A : RustAlloc) (a : BitVec 64)
    (r : InvalidMessageReason) :
    invalidMessageStrAt A a r ⊢ ∃∗ bs : List (BitVec 8), vecU8 A a bs := by
  cases r with
  | tooFarInFuture =>
    simp only [invalidMessageStrAt]
    exact Entails.sepExists_right tooFarInFutureStr (Entails.refl _)
  | macFailed =>
    simp only [invalidMessageStrAt]
    exact Entails.sepExists_right macFailedStr (Entails.refl _)
  | pqRatchet =>
    simp only [invalidMessageStrAt]
    exact Entails.refl _
  | badCiphertext =>
    simp only [invalidMessageStrAt]
    exact Entails.refl _
  | decryptionFailed =>
    simp only [invalidMessageStrAt]
    rw [← sepConj_emp ⌜False⌝]
    exact Entails.pure_left nofun

private theorem speAt_invalidMessage_expose (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) (t : MessageType) (r : InvalidMessageReason) :
    SatEntails (speAt A fnName a (.invalidMessage t r))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord 24) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  apply SatEntails.of_entails
  simp only [speAt]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (invalidMessageStrAt_entails_vecU8 A (a + 8#64) r)
      (spe_u8_at_32_entails_16 a (msgTypeByte t)))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_expose A a bs)) ?_
  simp only [sepExists_sepConj_right]
  exact Entails.refl _

private theorem spe_str_pre_weaken (A : RustAlloc)
    (a : BitVec 64) {ro_tbl ro_byte : SepProp} (r : RecErr) (i : Nat) (w : BitVec 64)
    (hw : speWord i = w)
    (hbyte : SatEntails ro_tbl ro_byte)
    (he : SatEntails (recErrAt A a r)
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord i) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)))
    (rest : SepProp) :
    SatEntails (ro_tbl ∗ (recErrAt A a r ∗ rest))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ w) ∗
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ro_byte ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ rest) := by
  subst hw
  refine SatEntails.trans (SatEntails.sepConj_mono hbyte (SatEntails.sepConj_mono_left he)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails.sepExists_elim; intro cap
  apply SatEntails.sepExists_elim; intro ptr
  refine SatEntails.sepExists_right cap (SatEntails.sepExists_right ptr ?_)
  exact SatEntails.of_eq (by ac_rfl)

private theorem spe_unit_pre_weaken (A : RustAlloc)
    (a : BitVec 64) {ro_tbl ro_byte : SepProp} (r : RecErr) (i : Nat) (w : BitVec 64)
    (hw : speWord i = w)
    (hbyte : SatEntails ro_tbl ro_byte)
    (he : SatEntails (recErrAt A a r) ((a ↦₆₄ speWord i) ∗ memRegion (a + 8#64) 40))
    (rest : SepProp) :
    SatEntails (ro_tbl ∗ (recErrAt A a r ∗ rest))
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro_byte ∗ rest) := by
  subst hw
  refine SatEntails.trans (SatEntails.sepConj_mono hbyte (SatEntails.sepConj_mono_left he)) ?_
  exact SatEntails.of_eq (by ac_rfl)

/-! ## 3. Single-Element Drop (+7820 → +7988) -/

private theorem stackAt_root_split_alloc (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack (rootStack - allocHookStack) (by decide)

private theorem segTail_dealloc_ok_of_raw {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustDeallocSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2 ^ 64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2 ^ 64))
      (rustDeallocSpec A) :=
  sub_ok_at_of_fnAddr hdealloc CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName
    (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by rw [(ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal"),
          (ls_stub% "__rustc::__rust_dealloc")])

private theorem segExit_drop_one_alloc {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr deallocName) (rustDeallocSpec A))
    (p : BitVec 64) (r : RecErr) (s0 s : State)
    (hpc_s : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 7820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp)
    (hsp_align : s.spAligned = true) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 7988#64) s
      (((img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168))) ↦ᵣ exitJumpTable) ∗
        (recErrAt A p r ∗
          (((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ p) ∗ ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 1#64) ∗
            stackAt s0.sp allocHookStack ∗ A.pool)))
      (fun sm Pm =>
        (Pm ⊢ memRegion p 48 ∗
          (((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ p) ∗ ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 1#64) ∗
            stackAt s0.sp allocHookStack ∗ A.pool)) ∧
        sm.sp = s.sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x20 = p ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hsp] using hsp_align
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  have hdealloc := segTail_dealloc_ok_of_raw hdealloc_raw
  clear hdealloc_raw
  have hadp :
      (((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 7840#64) &&&
        bv% (2 ^ 64 - 4096)) + bv% (page% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 15) - page% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 7840)) = img.base + bv% (page% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 15)) :=
    adrp_exitJumpTable_eq_local hb (by rw [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn])
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName] at *
  segTail_fetches_cli img.base (Rust.withPanics ext) hfn 7820 108
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "libsignal_cli_ratchet::decrypt_signal" = entry
  examples_hide_fetches
  cases r with
  | version v =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A p (.version v) 6 9223372036854775814#64 rfl
        (exitJumpTable_byte img.base 6 (bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 21)) 0#8 (by decide) (by rfl_kernel) (by rfl_kernel))
        (SatEntails.of_entails (by simp only [recErrAt]; exact sepConj_mono_right (spe_u32_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (spe_noop_after_weaken _ _ _ _) ?_
    wp_done
  | spe e =>
    cases e with
    | panic =>
      simp only [recErrAt, speAt]
      exact SepWP.false_elim
    | invalidState =>
      refine SepWP.weaken_pre_sat
        (spe_str_pre_weaken A p (.spe .invalidState) 1 9223372036854775809#64 rfl
          (exitJumpTable_byte img.base 1 (bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 16)) 13#8 (by decide) (by rfl_kernel) (by rfl_kernel))
          (by simpa only [recErrAt] using speAt_invalidState_expose A (utf8 "decrypt") p) _) ?_
      wp_pull_exists
      rename_i cap ptr
      by_cases hcap : cap = 0#64
      · simp only [hcap, beq_self_eq_true, ↓reduceIte, emp_sepConj]
        wp_steps
        refine SepWP.weaken_pre_sat (spe_str_after_weaken _ _ _ _ _ _) ?_
        wp_done
      · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
        simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
        wp_steps
        refine SepWP.weaken_pre_sat (spe_str_after_weaken _ _ _ _ _ _) ?_
        wp_apply
        wp_steps
        refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          ⟨?_, by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
        rw [hsp, show s0.sp + 1496#64 + 8#64 = s0.sp + 1504#64 by bv_omega,
          show s0.sp + 1496#64 + 16#64 = s0.sp + 1512#64 by bv_omega]
        exact Entails.of_eq (by ac_rfl)
    | invalidMessage t r =>
      refine SepWP.weaken_pre_sat
        (spe_str_pre_weaken A p (.spe (.invalidMessage t r)) 24 9223372036854775832#64 rfl
          (exitJumpTable_byte img.base 24 (bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 39)) 13#8 (by decide) (by rfl_kernel) (by rfl_kernel))
          (by simpa only [recErrAt] using speAt_invalidMessage_expose A (utf8 "decrypt") p t r) _) ?_
      wp_pull_exists
      rename_i cap ptr
      by_cases hcap : cap = 0#64
      · simp only [hcap, beq_self_eq_true, ↓reduceIte, emp_sepConj]
        wp_steps
        refine SepWP.weaken_pre_sat (spe_str_after_weaken _ _ _ _ _ _) ?_
        wp_done
      · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
        simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
        wp_steps
        refine SepWP.weaken_pre_sat (spe_str_after_weaken _ _ _ _ _ _) ?_
        wp_apply
        wp_steps
        refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          ⟨?_, by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
        rw [hsp, show s0.sp + 1496#64 + 8#64 = s0.sp + 1504#64 by bv_omega,
          show s0.sp + 1496#64 + 16#64 = s0.sp + 1512#64 by bv_omega]
        exact Entails.of_eq (by ac_rfl)
    | invalidProtobufEncoding =>
      refine SepWP.weaken_pre_sat
        (spe_unit_pre_weaken A p (.spe .invalidProtobufEncoding) 2 9223372036854775810#64 rfl
          (exitJumpTable_byte img.base 2 (bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 17)) 0#8 (by decide) (by rfl_kernel) (by rfl_kernel))
          (SatEntails.refl _) _) ?_
      wp_steps
      refine SepWP.weaken_pre_sat (spe_noop_after_weaken _ _ _ _) ?_
      wp_done
    | ciphertextMessageTooShort n =>
      refine SepWP.weaken_pre_sat
        (spe_unit_pre_weaken A p (.spe (.ciphertextMessageTooShort n)) 3 9223372036854775811#64 rfl
          (exitJumpTable_byte img.base 3 (bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 18)) 0#8 (by decide) (by rfl_kernel) (by rfl_kernel))
          (SatEntails.of_entails (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
      wp_steps
      refine SepWP.weaken_pre_sat (spe_noop_after_weaken _ _ _ _) ?_
      wp_done
    | legacyCiphertextVersion v =>
      refine SepWP.weaken_pre_sat
        (spe_unit_pre_weaken A p (.spe (.legacyCiphertextVersion v)) 4 9223372036854775812#64 rfl
          (exitJumpTable_byte img.base 4 (bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 19)) 0#8 (by decide) (by rfl_kernel) (by rfl_kernel))
          (SatEntails.of_entails (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
      wp_steps
      refine SepWP.weaken_pre_sat (spe_noop_after_weaken _ _ _ _) ?_
      wp_done
    | unrecognizedCiphertextVersion v =>
      refine SepWP.weaken_pre_sat
        (spe_unit_pre_weaken A p (.spe (.unrecognizedCiphertextVersion v)) 5 9223372036854775813#64 rfl
          (exitJumpTable_byte img.base 5 (bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 20)) 0#8 (by decide) (by rfl_kernel) (by rfl_kernel))
          (SatEntails.of_entails (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
      wp_steps
      refine SepWP.weaken_pre_sat (spe_noop_after_weaken _ _ _ _) ?_
      wp_done
    | noKeyTypeIdentifier =>
      refine SepWP.weaken_pre_sat
        (spe_unit_pre_weaken A p (.spe .noKeyTypeIdentifier) 7 9223372036854775815#64 rfl
          (exitJumpTable_byte img.base 7 (bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 22)) 0#8 (by decide) (by rfl_kernel) (by rfl_kernel))
          (SatEntails.refl _) _) ?_
      wp_steps
      refine SepWP.weaken_pre_sat (spe_noop_after_weaken _ _ _ _) ?_
      wp_done
    | badKeyType t =>
      refine SepWP.weaken_pre_sat
        (spe_unit_pre_weaken A p (.spe (.badKeyType t)) 8 9223372036854775816#64 rfl
          (exitJumpTable_byte img.base 8 (bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 23)) 0#8 (by decide) (by rfl_kernel) (by rfl_kernel))
          (SatEntails.of_entails (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
      wp_steps
      refine SepWP.weaken_pre_sat (spe_noop_after_weaken _ _ _ _) ?_
      wp_done
    | badKeyLength n =>
      refine SepWP.weaken_pre_sat
        (spe_unit_pre_weaken A p (.spe (.badKeyLength n)) 9 9223372036854775817#64 rfl
          (exitJumpTable_byte img.base 9 (bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 24)) 0#8 (by decide) (by rfl_kernel) (by rfl_kernel))
          (SatEntails.of_entails (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
      wp_steps
      refine SepWP.weaken_pre_sat (spe_noop_after_weaken _ _ _ _) ?_
      wp_done
    | invalidKeyAgreement =>
      refine SepWP.weaken_pre_sat
        (spe_unit_pre_weaken A p (.spe .invalidKeyAgreement) 10 9223372036854775818#64 rfl
          (exitJumpTable_byte img.base 10 (bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 25)) 0#8 (by decide) (by rfl_kernel) (by rfl_kernel))
          (SatEntails.refl _) _) ?_
      wp_steps
      refine SepWP.weaken_pre_sat (spe_noop_after_weaken _ _ _ _) ?_
      wp_done
    | invalidSessionStructure r =>
      refine SepWP.weaken_pre_sat
        (spe_unit_pre_weaken A p (.spe (.invalidSessionStructure r)) 20 9223372036854775828#64 rfl
          (exitJumpTable_byte img.base 20 (bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 35)) 0#8 (by decide) (by rfl_kernel) (by rfl_kernel))
          (by simp only [recErrAt, speAt]; exact SatEntails.sepConj_mono_right (spe_strRef_at_8_entails_40 _ _)) _) ?_
      wp_steps
      refine SepWP.weaken_pre_sat (spe_noop_after_weaken _ _ _ _) ?_
      wp_done
    | duplicatedMessage idx c =>
      refine SepWP.weaken_pre_sat
        (spe_unit_pre_weaken A p (.spe (.duplicatedMessage idx c)) 23 9223372036854775831#64 rfl
          (exitJumpTable_byte img.base 23 (bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 38)) 0#8 (by decide) (by rfl_kernel) (by rfl_kernel))
          (SatEntails.of_entails (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u32x2_at_8_entails_40 _ _ _))) _) ?_
      wp_steps
      refine SepWP.weaken_pre_sat (spe_noop_after_weaken _ _ _ _) ?_
      wp_done
  | iscmk =>
    refine SepWP.weaken_pre_sat
      (spe_unit_pre_weaken A p .iscmk 20 9223372036854775828#64 rfl
        (exitJumpTable_byte img.base 20 (bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168) + 35)) 0#8 (by decide) (by rfl_kernel) (by rfl_kernel))
        (iscmk_entails_40 A p) _) ?_
    wp_steps
    refine SepWP.weaken_pre_sat (spe_noop_after_weaken _ _ _ _) ?_
    wp_done

/-! ## 4. Frame Folding and `segExit_ok_alloc` (+7820 → +8016) -/

private theorem frame_low_entails_0xa0 (sp : BitVec 64) (w80 w88 w90 : BitVec 64) (w9c : BitVec 32) :
    memRegion sp 0x80 ∗ ((sp + 0x80#64) ↦₆₄ w80) ∗ ((sp + 0x88#64) ↦₆₄ w88) ∗
      ((sp + 0x90#64) ↦₆₄ w90) ∗ memRegion (sp + 0x98#64) 4 ∗ ((sp + 0x9c#64) ↦₃₂ w9c) ⊢
      memRegion sp 0xa0 := by
  rw [show (0xa0 : Nat) = 0x80 + 32 from rfl, memRegion_split sp 0x80 32 (by decide),
      show (32 : Nat) = 8 + 24 from rfl, memRegion_split (sp + BitVec.ofNat 64 0x80) 8 24 (by decide),
      show (24 : Nat) = 8 + 16 from rfl, memRegion_split (sp + BitVec.ofNat 64 0x80 + BitVec.ofNat 64 8) 8 16 (by decide),
      show (16 : Nat) = 8 + 8 from rfl, memRegion_split (sp + BitVec.ofNat 64 0x80 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 8 8 (by decide),
      show (8 : Nat) = 4 + 4 from rfl, memRegion_split (sp + BitVec.ofNat 64 0x80 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 4 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_right (pointsTo32_entails_memRegion _ _)))))

private theorem frame_high_entails_0x920 (sp : BitVec 64)
    (w5b0 : BitVec 64) (b5bc : BitVec 8) (w5c0 w5c8 w5d0 w5d8 w5e0 w5e8 : BitVec 64) :
    memRegion (sp + 0x4e0#64) 0xd0 ∗
      ((sp + 0x5b0#64) ↦₆₄ w5b0) ∗ memRegion (sp + 0x5b8#64) 4 ∗
      ((sp + 0x5bc#64) ↦₈ b5bc) ∗ memRegion (sp + 0x5bd#64) 3 ∗
      ((sp + 0x5c0#64) ↦₆₄ w5c0) ∗ ((sp + 0x5c8#64) ↦₆₄ w5c8) ∗
      ((sp + 0x5d0#64) ↦₆₄ w5d0) ∗
      ((sp + 0x5d8#64) ↦₆₄ w5d8) ∗ ((sp + 0x5d8#64 + 8#64) ↦₆₄ w5e0) ∗
      ((sp + 0x5d8#64 + 16#64) ↦₆₄ w5e8) ∗
      memRegion (sp + 0x5f0#64) 0x6b0 ∗ memRegion (sp + 0xca0#64) 344 ∗
      memRegion (sp + 0xdf8#64) 8 ⊢
      memRegion (sp + 0x4e0#64) 0x920 := by
  rw [show (0x920 : Nat) = 0xd0 + 2128 from rfl, memRegion_split (sp + 0x4e0#64) 0xd0 2128 (by decide),
      show (2128 : Nat) = 8 + 2120 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0) 8 2120 (by decide),
      show (2120 : Nat) = 4 + 2116 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8) 4 2116 (by decide),
      show (2116 : Nat) = 1 + 2115 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4) 1 2115 (by decide),
      show (2115 : Nat) = 3 + 2112 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1) 3 2112 (by decide),
      show (2112 : Nat) = 8 + 2104 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 3) 8 2104 (by decide),
      show (2104 : Nat) = 8 + 2096 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8) 8 2096 (by decide),
      show (2096 : Nat) = 8 + 2088 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 8 2088 (by decide),
      show (2088 : Nat) = 8 + 2080 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 8 2080 (by decide),
      show (2080 : Nat) = 8 + 2072 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 8 2072 (by decide),
      show (2072 : Nat) = 8 + 2064 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 8 2064 (by decide),
      show (2064 : Nat) = 0x6b0 + 352 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 0x6b0 352 (by decide),
      show (352 : Nat) = 344 + 8 from rfl, memRegion_split (sp + 0x4e0#64 + BitVec.ofNat 64 0xd0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 3 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 0x6b0) 344 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono (pointsTo8_entails_memRegion _ _)
      (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))))))))))

private def recFrameRest (A : RustAlloc) (img : Obj.Image) (x : RecordDecryptGhost)
    (sp : BitVec 64) : SepProp :=
  memRegion sp 0x80 ∗
  ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗ ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
  memRegion (sp + 0x98#64) 4 ∗ ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
  memRegion (sp + 0x4e0#64) 0xd0 ∗
  ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x5b8#64) 4 ∗
  ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗ memRegion (sp + 0x5bd#64) 3 ∗
  ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
  ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗
  memRegion (sp + 0x5f0#64) 0x6b0 ∗ memRegion (sp + 0xdf8#64) 8 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ logOff img ∗
  memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - allocHookStack)

private theorem recFrame_split_alloc (A : RustAlloc) (img : Obj.Image) (x : RecordDecryptGhost)
    (sp : BitVec 64) :
    recFrame A img x sp =
      recFrameRest A img x sp ∗ stackAt sp allocHookStack ∗ A.pool := by
  unfold recFrame recFrameRest
  rw [stackAt_root_split_alloc sp]
  ac_rfl

private theorem recPost_of_frame_aux {A : RustAlloc} {img : Obj.Image}
    (x : RecordDecryptGhost) (S_sess resSlot tape R : SepProp) (s0 sf : State)
    (w_cap w_ptr w_len : BitVec 64)
    (hm : sf.mem ⊨
      recFrame A img x s0.sp ∗
      ((s0.sp + 0x5d8#64) ↦₆₄ w_cap) ∗ ((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ w_ptr) ∗
      ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ w_len) ∗
      memRegion (s0.sp + 0xca0#64) 344 ∗
      S_sess ∗ resSlot ∗ tape ∗ R) :
    sf.mem ⊨
      memRegion s0.sp 0xa0 ∗
      ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
      ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
      S_sess ∗ resSlot ∗
      memRegion (s0.sp + 0x4e0#64) 0x920 ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      tape ∗ logOff img ∗ stackAt s0.sp rootStack ∗ A.pool ∗ R := by
  have hm_rearr : sf.mem ⊨
      (memRegion s0.sp 0x80 ∗ ((s0.sp + 0x80#64) ↦₆₄ x.sret) ∗ ((s0.sp + 0x88#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x90#64) ↦₆₄ x.msgA) ∗ memRegion (s0.sp + 0x98#64) 4 ∗
        ((s0.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32)) ∗
      ((memRegion (s0.sp + 0x4e0#64) 0xd0 ∗
        ((s0.sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (s0.sp + 0x5b8#64) 4 ∗
        ((s0.sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗ memRegion (s0.sp + 0x5bd#64) 3 ∗
        ((s0.sp + 0x5c0#64) ↦₆₄ (s0.sp + 0x5bc#64)) ∗ ((s0.sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
        ((s0.sp + 0x5d0#64) ↦₆₄ (s0.sp + 0x5b0#64)) ∗
        ((s0.sp + 0x5d8#64) ↦₆₄ w_cap) ∗ ((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ w_ptr) ∗
        ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ w_len) ∗
        memRegion (s0.sp + 0x5f0#64) 0x6b0 ∗ memRegion (s0.sp + 0xca0#64) 344 ∗
        memRegion (s0.sp + 0xdf8#64) 8) ∗
       (((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
        S_sess ∗ resSlot ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        tape ∗ logOff img ∗ stackAt s0.sp rootStack ∗ A.pool ∗ R)) := by
    dsimp only [recFrame] at hm
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  clear hm
  have hm_fold := Satisfies.mono
    (sepConj_mono (frame_low_entails_0xa0 s0.sp x.sret x.locA x.msgA _)
      (sepConj_mono_left (frame_high_entails_0x920 s0.sp x.remA (msgTypeByte .whisper)
        (s0.sp + 0x5bc#64) x.msgA (s0.sp + 0x5b0#64) w_cap w_ptr w_len)))
    hm_rearr
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm_fold

private theorem segExit_main_alloc {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr deallocName) (rustDeallocSpec A))
    (x : RecordDecryptGhost) (S_sess resSlot tape R : SepProp) (s0 s : State)
    (hpc_s : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Record.recJPC img)
    (hmeta : recMeta img s0 s)
    (hno_pan : (x.model C S uuidTryParse).1 ≠ .error .panic)
    (hx26 : s.readReg64 .x26 = s0.sp + 0xa0#64)
    (hx27 : s.readReg64 .x27 = x.sret)
    (hx28 : s.readReg64 .x28 = recordResultTag (x.model C S uuidTryParse).1)
    (hmem : s.mem ⊨ recFrame A img x s0.sp ∗ S_sess ∗ resSlot ∗
      (∃∗ errs : List RecErr, errsAt A (s0.sp + 0x5d8#64) errs) ∗ memRegion (s0.sp + 0xca0#64) 344 ∗
      tape ∗ R)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ sf, Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
      sf.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img ∧ sf.status = .Running ∧
      calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
      ((x.model C S uuidTryParse).1 ≠ .error .panic ∧ sf.trace = s0.trace ∧ sf.sp = s0.sp ∧
        sf.readReg64 .x29 = s0.readReg64 .x29 ∧ sf.readReg64 .x27 = x.sret ∧
        sf.readReg64 .x26 = s0.sp + 0xa0#64 ∧
        sf.readReg64 .x28 = recordResultTag (x.model C S uuidTryParse).1) ∧
      (sf.mem ⊨
        memRegion s0.sp 0xa0 ∗
        ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
        S_sess ∗ resSlot ∗
        memRegion (s0.sp + 0x4e0#64) 0x920 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        tape ∗ logOff img ∗ stackAt s0.sp rootStack ∗ A.pool ∗ R) := by
  obtain ⟨hrun, hsp, hsp_align, hx29, htrace, hfl, _hsym, hvregs⟩ := hmeta
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hsp] using hsp_align
  have hro : img.RoDataLoaded s.mem := (Obj.Image.frozenLoaded_iff.mp hfl).2.1
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Record.recJPC, entryOf_eq_tripleRatchetProgAtExt ext himg CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName] at hpc_s
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  have hdealloc := segTail_dealloc_ok_of_raw hdealloc_raw
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  obtain ⟨errs, hmem⟩ := hmem
  rcases errs with _ | ⟨r_err, _ | ⟨r2, rest⟩⟩
  · have hmem_nil : s.mem ⊨
        (((s0.sp + 0x5d8#64) ↦₆₄ 0#64) ∗ ((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ 8#64) ∗
         ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 0#64)) ∗
        (recFrame A img x s0.sp ∗
         memRegion (s0.sp + 0xca0#64) 344 ∗
         S_sess ∗ resSlot ∗ tape ∗ R) := by
      dsimp only [errsAt] at hmem
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    clear hmem
    have hwp_nil : SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 8016#64) s
        (((s0.sp + 0x5d8#64) ↦₆₄ 0#64) ∗ ((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ 8#64) ∗
         ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 0#64))
        (fun sf Pf =>
          Pf = (((s0.sp + 0x5d8#64) ↦₆₄ 0#64) ∗ ((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ 8#64) ∗
            ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 0#64)) ∧
          sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
          sf.readReg64 .x26 = s0.sp + 0xa0#64 ∧ sf.readReg64 .x27 = x.sret ∧
          sf.readReg64 .x28 = recordResultTag (x.model C S uuidTryParse).1 ∧
          sf.readReg64 .x29 = s0.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0) := by
      clear hdealloc_raw hdealloc
      dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName] at *
      segTail_fetches_cli img.base (Rust.withPanics ext) hfn 7820 12
      segTail_fetches_cli img.base (Rust.withPanics ext) hfn 7988 8
      clear hfn
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr
        "libsignal_cli_ratchet::decrypt_signal" = entry
      examples_hide_fetches
      wp_steps
      exact SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        ⟨rfl, by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *]⟩
    rcases hwp_nil.elim hmem_nil hL with
      ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, Pf, hmf, rfl, hsp_sf, htr_sf, hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩ | ⟨_, hoom⟩⟩
    swap; · exact (not_satisfies_false_sepConj hoom).elim
    refine ⟨sf, hsteps, ?_, hrun_sf, hvregs_sf, ⟨hno_pan, htr_sf, hsp_sf, hx29_sf, hx27_sf, hx26_sf, hx28_sf⟩, ?_⟩
    · rw [CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit, entryOf_eq_tripleRatchetProgAtExt ext himg CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName]
      exact hpc_sf
    · apply recPost_of_frame_aux x S_sess resSlot tape R s0 sf 0#64 8#64 0#64
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf
  · dsimp only [errsAt] at hmem
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
    obtain ⟨p, hmem⟩ := hmem
    have hmem_ro := rodata_exitJumpTable_intro himg hro hmem
    clear hmem
    rw [recFrame_split_alloc A img x s0.sp] at hmem_ro
    have hmem_p : s.mem ⊨ ⌜p ≠ 0⌝ ∗
        ((((img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2164) (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 2168))) ↦ᵣ exitJumpTable) ∗
          (recErrAt A p r_err ∗
            (((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ p) ∗ ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 1#64) ∗
              stackAt s0.sp allocHookStack ∗ A.pool))) ∗
         (((s0.sp + 0x5d8#64) ↦₆₄ 4#64) ∗ A.live p 192 8 ∗ memRegion (p + 48#64) 144 ∗
          recFrameRest A img x s0.sp ∗
          memRegion (s0.sp + 0xca0#64) 344 ∗
          S_sess ∗ resSlot ∗ tape ∗ R)) := by
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem_ro
    clear hmem_ro
    rw [satisfies_pure_sepConj] at hmem_p
    obtain ⟨_hp, hmem_drop⟩ := hmem_p
    have hdrop := segExit_drop_one_alloc himg hdealloc_raw p r_err s0 s hpc_s hrun hsp hsp_align
    rcases hdrop.elim hmem_drop hL with ⟨sm, hsteps1, ⟨hpc_sm, hrun_sm, Pm, hmm, hent_m, hsp_sm, htr_sm, hx20_sm,
      hx26_sm, hx27_sm, hx28_sm, hx29_sm, hvregs_sm0⟩ | ⟨_, hoom⟩⟩
    swap; · exact (not_satisfies_false_sepConj hoom).elim
    clear hmem_drop hdrop hdealloc_raw
    have hvregs_sm : calleeSavedVRegs sm = calleeSavedVRegs s0 := hvregs_sm0.trans hvregs
    have hmm' := Satisfies.mono (sepConj_mono_left hent_m) hmm
    clear hmm hent_m
    have h192 : memRegion p 192 = memRegion p 48 ∗ memRegion (p + 48#64) 144 := by
      simpa using memRegion_split p 48 144 (by decide)
    have hmm_dealloc : sm.mem ⊨
        (((s0.sp + 0x5d8#64) ↦₆₄ 4#64) ∗ A.live p 192 8 ∗ memRegion p 192 ∗
         stackAt s0.sp allocHookStack ∗ A.pool) ∗
        (((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ p) ∗ ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 1#64) ∗
         recFrameRest A img x s0.sp ∗
         memRegion (s0.sp + 0xca0#64) 344 ∗
         S_sess ∗ resSlot ∗ tape ∗ R) := by
      rw [h192]
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmm'
    clear hmm'
    have hsp_sm0 : sm.sp = s0.sp := hsp_sm.trans hsp
    have hwp_dealloc : SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 8016#64) sm
        (((s0.sp + 0x5d8#64) ↦₆₄ 4#64) ∗ A.live p 192 8 ∗ memRegion p 192 ∗
         stackAt s0.sp allocHookStack ∗ A.pool)
        (fun sf Pf =>
          (Pf ⊢ ((s0.sp + 0x5d8#64) ↦₆₄ 4#64) ∗ stackAt s0.sp allocHookStack ∗ A.pool) ∧
          sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
          sf.readReg64 .x26 = s0.sp + 0xa0#64 ∧ sf.readReg64 .x27 = x.sret ∧
          sf.readReg64 .x28 = recordResultTag (x.model C S uuidTryParse).1 ∧
          sf.readReg64 .x29 = s0.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0) := by
      dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName] at *
      segTail_fetches_cli img.base (Rust.withPanics ext) hfn 7988 28
      clear hfn
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr
        "libsignal_cli_ratchet::decrypt_signal" = entry
      examples_hide_fetches
      wp_steps
      wp_apply
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        ⟨?_, by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *]⟩
      rw [hsp_sm0]
      exact Entails.of_eq (by ac_rfl)
    rcases hwp_dealloc.elim hmm_dealloc (hsteps1.codeLoaded hL) with
      ⟨sf, hsteps2, ⟨hpc_sf, hrun_sf, Pf, hmf, hent_f, hsp_sf, htr_sf,
        hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩ | ⟨_, hoom⟩⟩
    rotate_left; · exact (not_satisfies_false_sepConj hoom).elim
    clear hmm_dealloc hwp_dealloc
    have hmf' := Satisfies.mono (sepConj_mono_left hent_f) hmf
    clear hmf hent_f
    refine ⟨sf, hsteps1.trans hsteps2, ?_, hrun_sf, hvregs_sf, ⟨hno_pan, htr_sf, hsp_sf, hx29_sf, hx27_sf, hx26_sf, hx28_sf⟩, ?_⟩
    · rw [CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit, entryOf_eq_tripleRatchetProgAtExt ext himg CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName]
      exact hpc_sf
    · apply recPost_of_frame_aux x S_sess resSlot tape R s0 sf 4#64 p 1#64
      rw [recFrame_split_alloc A img x s0.sp]
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf'
  · dsimp only [errsAt] at hmem
    have hfalse : s.mem ⊨ ⌜False⌝ ∗
        (recFrame A img x s0.sp ∗ S_sess ∗ resSlot ∗
         memRegion (s0.sp + 0xca0#64) 344 ∗ tape ∗ R) := by
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    rw [satisfies_pure_sepConj] at hfalse
    exact False.elim hfalse.1

/-- **SegExit (`+7820 → +8016`)** under `rustDeallocSpec A` (`4096` B). -/
theorem segExit_ok_dealloc {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr deallocName) (rustDeallocSpec A))
    (x : RecordDecryptGhost) (R : SepProp) (s0 s : State)
    (hJ : CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ sf, Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
      regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 sf := by
  obtain ⟨hpc_s, hmeta, hno_pan, hx26, hx27, hx28, hmem⟩ := hJ
  obtain ⟨sf, hsteps, hpc_sf, hrun_sf, hvregs_sf, hpure_sf, hmem_sf⟩ :=
    segExit_main_alloc himg hdealloc x _ _ _ R s0 s hpc_s hmeta hno_pan hx26 hx27 hx28 hmem hL
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hrun_sf, hvregs_sf, ?_⟩⟩
  simp only [CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpure_sf, hmem_sf⟩

/-- **SegExit (`+7820 → +8016`)** under `AllocContracts img.base A ext`. -/
theorem segExit_ok_alloc {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (x : RecordDecryptGhost) (R : SepProp) (s0 s : State)
    (hJ : CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x R s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ sf, Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
      regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 sf :=
  segExit_ok_dealloc himg hA.dealloc x R s0 s hJ hL

end CryptoVerification.Cli.LibsignalSpqrV1.M4
