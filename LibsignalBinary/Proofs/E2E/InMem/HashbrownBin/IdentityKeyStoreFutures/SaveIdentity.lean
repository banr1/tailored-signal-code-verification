/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.Common
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
public import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.DecodesSave
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.HashOne
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Skeleton
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply

/-!
# `InMemIdentityKeyStore::save_identity::{closure#0}` (`0x077cc`)

Proves `saveIdentityEmpty_ok'` and `saveIdentitySingleHit_ok'`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.SipHashBin
open CryptoVerification.E2E.InMem.HashbrownBin

namespace SaveIdentity

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff hashAddrBv
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : Arm64.State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : Arm64.State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := Arm64.State.readReg64_setPC s pc r
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

theorem sepWP_exists_elim {α : Sort _} {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : α → SepProp} {post : Arm64.State → SepProp → Prop}
    (h : ∀ a, SepWP prog pc s (P a) post) : SepWP prog pc s (∃∗ a, P a) post :=
  HashOne.sepWP_exists_elim h

theorem sepWP_pure_left_elim {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : Prop} {Q : SepProp} {post : Arm64.State → SepProp → Prop}
    (h : P → SepWP prog pc s Q post) : SepWP prog pc s (⌜P⌝ ∗ Q) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2

theorem sepWP_extract_pure {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : Prop} {Q F : SepProp} {post : Arm64.State → SepProp → Prop}
    (heq : Q = ⌜P⌝ ∗ F) (h : P → SepWP prog pc s F post) : SepWP prog pc s Q post := by
  rw [heq]; exact sepWP_pure_left_elim h

@[arm64_norm, wp_norm]
theorem sp_save_prologue_eqs (sp : BitVec 64) :
    sp + bv% (2 ^ 64 - 240) = sp - 240#64 ∧ sp - 240#64 + 8#64 = sp - 232#64 ∧
    sp - 240#64 + 16#64 = sp - 224#64 ∧ sp - 240#64 + 31#64 = sp - 209#64 ∧
    sp - 240#64 + 64#64 = sp - 176#64 ∧ sp - 240#64 + 88#64 = sp - 152#64 ∧
    sp - 240#64 + 128#64 = sp - 112#64 ∧ sp - 112#64 + 8#64 = sp - 104#64 ∧
    sp - 240#64 + 144#64 = sp - 96#64 ∧ sp - 96#64 + 8#64 = sp - 88#64 ∧
    sp - 240#64 + 144#64 + 8#64 = sp - 88#64 ∧ sp - 240#64 + 160#64 = sp - 80#64 ∧
    sp - 240#64 + 160#64 + 8#64 = sp - 72#64 ∧ sp - 240#64 + 176#64 = sp - 64#64 ∧
    sp - 240#64 + 176#64 + 8#64 = sp - 56#64 ∧ sp - 240#64 + 192#64 = sp - 48#64 ∧
    sp - 240#64 + 192#64 + 8#64 = sp - 40#64 ∧ sp - 240#64 + 208#64 = sp - 32#64 ∧
    sp - 240#64 + 208#64 + 8#64 = sp - 24#64 ∧ sp - 240#64 + 224#64 = sp - 16#64 ∧
    sp - 240#64 + 224#64 + 8#64 = sp - 8#64 ∧ sp - 240#64 + 240#64 = sp ∧
    sp - 96#64 - 48#64 = sp - 144#64 ∧ sp - 96#64 + bv% (2 ^ 64 - 48) = sp - 144#64 ∧
    sp - 144#64 + 8#64 = sp - 136#64 ∧ sp - 144#64 + 16#64 = sp - 128#64 ∧
    sp - 128#64 + 8#64 = sp - 120#64 := by
  refine ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega⟩

theorem entails_sepExists_intro {α : Sort _} {P : SepProp} {Q : α → SepProp} (a : α)
    (h : P ⊢ Q a) : P ⊢ (∃∗ x, Q x) := Entails.sepExists_right a h

theorem stackAt_save_eq (sp : BitVec 64) :
    stackAt sp saveIdentityClosureStack =
      memRegion (sp - 17184#64) 16944 ∗ memRegion (sp - 240#64) 8 ∗
      (∃∗ c_sp8 : BitVec 64, ∃∗ c_sp16 : BitVec 64,
        ((sp - 232#64) ↦₆₄ c_sp8) ∗ ((sp - 224#64) ↦₆₄ c_sp16)) ∗
      memRegion (sp - 216#64) 7 ∗ memRegion (sp - 209#64) 33 ∗ memRegion (sp - 176#64) 24 ∗
      (∃∗ c_sp88 : BitVec 8, (sp - 152#64) ↦₈ c_sp88) ∗ memRegion (sp - 151#64) 7 ∗
      (∃∗ c_sp96 : BitVec 64, ∃∗ c_sp104 : BitVec 64, ∃∗ c_sp112 : BitVec 64, ∃∗ c_sp120 : BitVec 64,
       ∃∗ c_d9 : BitVec 64, ∃∗ c_d8 : BitVec 64, ∃∗ c_x29 : BitVec 64, ∃∗ c_x30 : BitVec 64,
       ∃∗ c_x28 : BitVec 64, ∃∗ c_x27 : BitVec 64, ∃∗ c_x26 : BitVec 64, ∃∗ c_x25 : BitVec 64,
       ∃∗ c_x24 : BitVec 64, ∃∗ c_x23 : BitVec 64, ∃∗ c_x22 : BitVec 64, ∃∗ c_x21 : BitVec 64,
       ∃∗ c_x20 : BitVec 64, ∃∗ c_x19 : BitVec 64,
        ((sp - 144#64) ↦₆₄ c_sp96) ∗ ((sp - 136#64) ↦₆₄ c_sp104) ∗
        ((sp - 128#64) ↦₆₄ c_sp112) ∗ ((sp - 120#64) ↦₆₄ c_sp120) ∗
        ((sp - 112#64) ↦₆₄ c_d9) ∗ ((sp - 104#64) ↦₆₄ c_d8) ∗
        ((sp - 96#64) ↦₆₄ c_x29) ∗ ((sp - 88#64) ↦₆₄ c_x30) ∗
        ((sp - 80#64) ↦₆₄ c_x28) ∗ ((sp - 72#64) ↦₆₄ c_x27) ∗
        ((sp - 64#64) ↦₆₄ c_x26) ∗ ((sp - 56#64) ↦₆₄ c_x25) ∗
        ((sp - 48#64) ↦₆₄ c_x24) ∗ ((sp - 40#64) ↦₆₄ c_x23) ∗
        ((sp - 32#64) ↦₆₄ c_x22) ∗ ((sp - 24#64) ↦₆₄ c_x21) ∗
        ((sp - 16#64) ↦₆₄ c_x20) ∗ ((sp - 8#64) ↦₆₄ c_x19)) := by
  simp only [stackAt, saveIdentityClosureStack, HashbrownBin.extHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (2 ^ 14 + 800)) (n := 16944) (k := 240) (b' := sp - 240#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 240#64) (n := 8) (k := 232) (b' := sp - 232#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 232#64) (n := 16) (k := 216) (b' := sp - 216#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 216#64) (n := 7) (k := 209) (b' := sp - 209#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 209#64) (n := 33) (k := 176) (b' := sp - 176#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 176#64) (n := 24) (k := 152) (b' := sp - 152#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 152#64) (n := 1) (k := 151) (b' := sp - 151#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 151#64) (n := 7) (k := 144) (b' := sp - 144#64) (by decide) (by bv_omega) (by decide)]
  change memRegion (sp - 17184#64) 16944 ∗ (memRegion (sp - 240#64) 8 ∗
    (memRegion (sp - 232#64) (8 * 2) ∗ (memRegion (sp - 216#64) 7 ∗
    (memRegion (sp - 209#64) 33 ∗ (memRegion (sp - 176#64) 24 ∗
    (memRegion (sp - 152#64) 1 ∗ (memRegion (sp - 151#64) 7 ∗
    memRegion (sp - 144#64) (8 * 18)))))))) = _
  rw [memRegion_cells (sp - 232#64) 2 (by decide), memRegion_one (sp - 152#64),
      memRegion_cells (sp - 144#64) 18 (by decide)]
  have hc2 : cells (sp - 232#64) 2 =
      (∃∗ c_sp8 : BitVec 64, ∃∗ c_sp16 : BitVec 64,
        ((sp - 232#64) ↦₆₄ c_sp8) ∗ ((sp - 224#64) ↦₆₄ c_sp16)) := by cells_unfold
  have hc18 : cells (sp - 144#64) 18 =
      (∃∗ c_sp96 : BitVec 64, ∃∗ c_sp104 : BitVec 64, ∃∗ c_sp112 : BitVec 64, ∃∗ c_sp120 : BitVec 64,
       ∃∗ c_d9 : BitVec 64, ∃∗ c_d8 : BitVec 64, ∃∗ c_x29 : BitVec 64, ∃∗ c_x30 : BitVec 64,
       ∃∗ c_x28 : BitVec 64, ∃∗ c_x27 : BitVec 64, ∃∗ c_x26 : BitVec 64, ∃∗ c_x25 : BitVec 64,
       ∃∗ c_x24 : BitVec 64, ∃∗ c_x23 : BitVec 64, ∃∗ c_x22 : BitVec 64, ∃∗ c_x21 : BitVec 64,
       ∃∗ c_x20 : BitVec 64, ∃∗ c_x19 : BitVec 64,
        ((sp - 144#64) ↦₆₄ c_sp96) ∗ ((sp - 136#64) ↦₆₄ c_sp104) ∗
        ((sp - 128#64) ↦₆₄ c_sp112) ∗ ((sp - 120#64) ↦₆₄ c_sp120) ∗
        ((sp - 112#64) ↦₆₄ c_d9) ∗ ((sp - 104#64) ↦₆₄ c_d8) ∗
        ((sp - 96#64) ↦₆₄ c_x29) ∗ ((sp - 88#64) ↦₆₄ c_x30) ∗
        ((sp - 80#64) ↦₆₄ c_x28) ∗ ((sp - 72#64) ↦₆₄ c_x27) ∗
        ((sp - 64#64) ↦₆₄ c_x26) ∗ ((sp - 56#64) ↦₆₄ c_x25) ∗
        ((sp - 48#64) ↦₆₄ c_x24) ∗ ((sp - 40#64) ↦₆₄ c_x23) ∗
        ((sp - 32#64) ↦₆₄ c_x22) ∗ ((sp - 24#64) ↦₆₄ c_x21) ∗
        ((sp - 16#64) ↦₆₄ c_x20) ∗ ((sp - 8#64) ↦₆₄ c_x19)) := by cells_unfold
  rw [hc2, hc18]

theorem stackAt_save_of_parts (sp : BitVec 64)
    (c_sp8 c_sp16 : BitVec 64) (c_sp88 : BitVec 8)
    (c_sp96 c_sp104 c_sp112 c_sp120 : BitVec 64)
    (c_d9 c_d8 c_x29 c_x30 c_x28 c_x27 c_x26 c_x25 c_x24 c_x23 c_x22 c_x21 c_x20 c_x19 : BitVec 64) :
    (memRegion (sp - 17184#64) 16944 ∗ memRegion (sp - 240#64) 8 ∗
      ((sp - 232#64) ↦₆₄ c_sp8) ∗ ((sp - 224#64) ↦₆₄ c_sp16) ∗
      memRegion (sp - 216#64) 7 ∗ memRegion (sp - 209#64) 33 ∗ memRegion (sp - 176#64) 24 ∗
      ((sp - 152#64) ↦₈ c_sp88) ∗ memRegion (sp - 151#64) 7 ∗
      ((sp - 144#64) ↦₆₄ c_sp96) ∗ ((sp - 136#64) ↦₆₄ c_sp104) ∗
      ((sp - 128#64) ↦₆₄ c_sp112) ∗ ((sp - 120#64) ↦₆₄ c_sp120) ∗
      ((sp - 112#64) ↦₆₄ c_d9) ∗ ((sp - 104#64) ↦₆₄ c_d8) ∗
      ((sp - 96#64) ↦₆₄ c_x29) ∗ ((sp - 88#64) ↦₆₄ c_x30) ∗
      ((sp - 80#64) ↦₆₄ c_x28) ∗ ((sp - 72#64) ↦₆₄ c_x27) ∗
      ((sp - 64#64) ↦₆₄ c_x26) ∗ ((sp - 56#64) ↦₆₄ c_x25) ∗
      ((sp - 48#64) ↦₆₄ c_x24) ∗ ((sp - 40#64) ↦₆₄ c_x23) ∗
      ((sp - 32#64) ↦₆₄ c_x22) ∗ ((sp - 24#64) ↦₆₄ c_x21) ∗
      ((sp - 16#64) ↦₆₄ c_x20) ∗ ((sp - 8#64) ↦₆₄ c_x19)) ⊢
    stackAt sp saveIdentityClosureStack := by
  rw [stackAt_save_eq sp]
  have h2 := entails_sepExists_intro c_sp8 (Q := fun x => ∃∗ c_sp16 : BitVec 64,
    ((sp - 232#64) ↦₆₄ x) ∗ ((sp - 224#64) ↦₆₄ c_sp16))
    (entails_sepExists_intro c_sp16 (Entails.refl _))
  have h1 : ((sp - 152#64) ↦₈ c_sp88) ⊢ (∃∗ c_sp88 : BitVec 8, (sp - 152#64) ↦₈ c_sp88) :=
    entails_sepExists_intro c_sp88 (Entails.refl _)
  have h18 :
      (((sp - 144#64) ↦₆₄ c_sp96) ∗ ((sp - 136#64) ↦₆₄ c_sp104) ∗
        ((sp - 128#64) ↦₆₄ c_sp112) ∗ ((sp - 120#64) ↦₆₄ c_sp120) ∗
        ((sp - 112#64) ↦₆₄ c_d9) ∗ ((sp - 104#64) ↦₆₄ c_d8) ∗
        ((sp - 96#64) ↦₆₄ c_x29) ∗ ((sp - 88#64) ↦₆₄ c_x30) ∗
        ((sp - 80#64) ↦₆₄ c_x28) ∗ ((sp - 72#64) ↦₆₄ c_x27) ∗
        ((sp - 64#64) ↦₆₄ c_x26) ∗ ((sp - 56#64) ↦₆₄ c_x25) ∗
        ((sp - 48#64) ↦₆₄ c_x24) ∗ ((sp - 40#64) ↦₆₄ c_x23) ∗
        ((sp - 32#64) ↦₆₄ c_x22) ∗ ((sp - 24#64) ↦₆₄ c_x21) ∗
        ((sp - 16#64) ↦₆₄ c_x20) ∗ ((sp - 8#64) ↦₆₄ c_x19)) ⊢
      (∃∗ c_sp96 : BitVec 64, ∃∗ c_sp104 : BitVec 64, ∃∗ c_sp112 : BitVec 64, ∃∗ c_sp120 : BitVec 64,
       ∃∗ c_d9 : BitVec 64, ∃∗ c_d8 : BitVec 64, ∃∗ c_x29 : BitVec 64, ∃∗ c_x30 : BitVec 64,
       ∃∗ c_x28 : BitVec 64, ∃∗ c_x27 : BitVec 64, ∃∗ c_x26 : BitVec 64, ∃∗ c_x25 : BitVec 64,
       ∃∗ c_x24 : BitVec 64, ∃∗ c_x23 : BitVec 64, ∃∗ c_x22 : BitVec 64, ∃∗ c_x21 : BitVec 64,
       ∃∗ c_x20 : BitVec 64, ∃∗ c_x19 : BitVec 64,
        ((sp - 144#64) ↦₆₄ c_sp96) ∗ ((sp - 136#64) ↦₆₄ c_sp104) ∗
        ((sp - 128#64) ↦₆₄ c_sp112) ∗ ((sp - 120#64) ↦₆₄ c_sp120) ∗
        ((sp - 112#64) ↦₆₄ c_d9) ∗ ((sp - 104#64) ↦₆₄ c_d8) ∗
        ((sp - 96#64) ↦₆₄ c_x29) ∗ ((sp - 88#64) ↦₆₄ c_x30) ∗
        ((sp - 80#64) ↦₆₄ c_x28) ∗ ((sp - 72#64) ↦₆₄ c_x27) ∗
        ((sp - 64#64) ↦₆₄ c_x26) ∗ ((sp - 56#64) ↦₆₄ c_x25) ∗
        ((sp - 48#64) ↦₆₄ c_x24) ∗ ((sp - 40#64) ↦₆₄ c_x23) ∗
        ((sp - 32#64) ↦₆₄ c_x22) ∗ ((sp - 24#64) ↦₆₄ c_x21) ∗
        ((sp - 16#64) ↦₆₄ c_x20) ∗ ((sp - 8#64) ↦₆₄ c_x19)) :=
    entails_sepExists_intro c_sp96 (entails_sepExists_intro c_sp104 (entails_sepExists_intro c_sp112
      (entails_sepExists_intro c_sp120 (entails_sepExists_intro c_d9 (entails_sepExists_intro c_d8
      (entails_sepExists_intro c_x29 (entails_sepExists_intro c_x30 (entails_sepExists_intro c_x28
      (entails_sepExists_intro c_x27 (entails_sepExists_intro c_x26 (entails_sepExists_intro c_x25
      (entails_sepExists_intro c_x24 (entails_sepExists_intro c_x23 (entails_sepExists_intro c_x22
      (entails_sepExists_intro c_x21 (entails_sepExists_intro c_x20 (entails_sepExists_intro c_x19
      (Entails.refl _))))))))))))))))))
  have hgroup :
      (memRegion (sp - 17184#64) 16944 ∗ memRegion (sp - 240#64) 8 ∗
        ((sp - 232#64) ↦₆₄ c_sp8) ∗ ((sp - 224#64) ↦₆₄ c_sp16) ∗
        memRegion (sp - 216#64) 7 ∗ memRegion (sp - 209#64) 33 ∗ memRegion (sp - 176#64) 24 ∗
        ((sp - 152#64) ↦₈ c_sp88) ∗ memRegion (sp - 151#64) 7 ∗
        ((sp - 144#64) ↦₆₄ c_sp96) ∗ ((sp - 136#64) ↦₆₄ c_sp104) ∗
        ((sp - 128#64) ↦₆₄ c_sp112) ∗ ((sp - 120#64) ↦₆₄ c_sp120) ∗
        ((sp - 112#64) ↦₆₄ c_d9) ∗ ((sp - 104#64) ↦₆₄ c_d8) ∗
        ((sp - 96#64) ↦₆₄ c_x29) ∗ ((sp - 88#64) ↦₆₄ c_x30) ∗
        ((sp - 80#64) ↦₆₄ c_x28) ∗ ((sp - 72#64) ↦₆₄ c_x27) ∗
        ((sp - 64#64) ↦₆₄ c_x26) ∗ ((sp - 56#64) ↦₆₄ c_x25) ∗
        ((sp - 48#64) ↦₆₄ c_x24) ∗ ((sp - 40#64) ↦₆₄ c_x23) ∗
        ((sp - 32#64) ↦₆₄ c_x22) ∗ ((sp - 24#64) ↦₆₄ c_x21) ∗
        ((sp - 16#64) ↦₆₄ c_x20) ∗ ((sp - 8#64) ↦₆₄ c_x19)) =
      (memRegion (sp - 17184#64) 16944 ∗ memRegion (sp - 240#64) 8 ∗
        (((sp - 232#64) ↦₆₄ c_sp8) ∗ ((sp - 224#64) ↦₆₄ c_sp16)) ∗
        memRegion (sp - 216#64) 7 ∗ memRegion (sp - 209#64) 33 ∗ memRegion (sp - 176#64) 24 ∗
        ((sp - 152#64) ↦₈ c_sp88) ∗ memRegion (sp - 151#64) 7 ∗
        (((sp - 144#64) ↦₆₄ c_sp96) ∗ ((sp - 136#64) ↦₆₄ c_sp104) ∗
          ((sp - 128#64) ↦₆₄ c_sp112) ∗ ((sp - 120#64) ↦₆₄ c_sp120) ∗
          ((sp - 112#64) ↦₆₄ c_d9) ∗ ((sp - 104#64) ↦₆₄ c_d8) ∗
          ((sp - 96#64) ↦₆₄ c_x29) ∗ ((sp - 88#64) ↦₆₄ c_x30) ∗
          ((sp - 80#64) ↦₆₄ c_x28) ∗ ((sp - 72#64) ↦₆₄ c_x27) ∗
          ((sp - 64#64) ↦₆₄ c_x26) ∗ ((sp - 56#64) ↦₆₄ c_x25) ∗
          ((sp - 48#64) ↦₆₄ c_x24) ∗ ((sp - 40#64) ↦₆₄ c_x23) ∗
          ((sp - 32#64) ↦₆₄ c_x22) ∗ ((sp - 24#64) ↦₆₄ c_x21) ∗
          ((sp - 16#64) ↦₆₄ c_x20) ∗ ((sp - 8#64) ↦₆₄ c_x19))) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono h2
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono h1 (sepConj_mono_right h18)))))))

theorem stackAt_save_ext_eq (sp : BitVec 64) :
    memRegion (sp - 17184#64) 16944 =
      memRegion (sp - 17184#64) 560 ∗ stackAt (sp - 240#64) HashbrownBin.extHookStack := by
  change memRegion (sp - 17184#64) (560 + 16384) =
    memRegion (sp - 17184#64) 560 ∗ memRegion (sp - 240#64 - 16384#64) 16384
  rw [memRegion_split (sp - 17184#64) 560 16384 (by decide),
      show sp - 17184#64 + BitVec.ofNat 64 560 = sp - 240#64 - 16384#64 by bv_omega]

theorem stackAt_save_insert_eq (sp : BitVec 64) :
    memRegion (sp - 17184#64) 16944 =
      memRegion (sp - 17184#64) 16 ∗ stackAt (sp - 240#64) hashMapIdInsertStack := by
  change memRegion (sp - 17184#64) (16 + 16928) =
    memRegion (sp - 17184#64) 16 ∗ memRegion (sp - 240#64 - 16928#64) 16928
  rw [memRegion_split (sp - 17184#64) 16 16928 (by decide),
      show sp - 17184#64 + BitVec.ofNat 64 16 = sp - 240#64 - 16928#64 by bv_omega]

theorem stackAt_save_hashOne_eq (sp : BitVec 64) :
    memRegion (sp - 17184#64) 16944 =
      memRegion (sp - 17184#64) 16832 ∗ stackAt (sp - 240#64) hashOneAddrStack := by
  change memRegion (sp - 17184#64) (16832 + 112) =
    memRegion (sp - 17184#64) 16832 ∗ memRegion (sp - 240#64 - 112#64) 112
  rw [memRegion_split (sp - 17184#64) 16832 112 (by decide),
      show sp - 17184#64 + BitVec.ofNat 64 16832 = sp - 240#64 - 112#64 by bv_omega]

theorem sret48_save_split_eq (sret : BitVec 64) :
    memRegion sret 48 =
      (∃∗ s_0 : BitVec 64, sret ↦₆₄ s_0) ∗
      (∃∗ s_8 : BitVec 32, (sret + 8#64) ↦₃₂ s_8) ∗
      memRegion (sret + 12#64) 36 := by
  rw [ProofLib.memRegion_split' (b := sret) (n := 8) (k := 40) (b' := sret + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sret + 8#64) (n := 4) (k := 36) (b' := sret + 12#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight sret,
      ProofLib.memRegion_four (sret + 8#64)]

theorem pollIdentityChangeResultAt_of_parts (sret : BitVec 64) (replaced : Bool) :
    ((sret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sret + 8#64) ↦₃₂ (if replaced then 1#32 else 0#32)) ∗
      memRegion (sret + 12#64) 36) ⊢ pollIdentityChangeResultAt sret replaced := Entails.refl _

theorem emptyTableAt_eq (base mp k0 k1 : BitVec 64) :
    emptyTableAt base mp k0 k1 =
      (mp ↦₆₄ (base + BitVec.ofNat 64 emptyCtrlGroupOff)) ∗ ((mp + 8#64) ↦₆₄ 0#64) ∗
      ((mp + 16#64) ↦₆₄ 0#64) ∗ ((mp + 24#64) ↦₆₄ 0#64) ∗
      ((mp + 32#64) ↦₆₄ k0) ∗ ((mp + 40#64) ↦₆₄ k1) := by
  have hadd : mp + 32#64 + 8#64 = mp + 40#64 := by bv_omega
  unfold emptyTableAt
  change (mp ↦₆₄ (base + BitVec.ofNat 64 emptyCtrlGroupOff)) ∗ ((mp + 8#64) ↦₆₄ 0#64) ∗
    ((mp + 16#64) ↦₆₄ 0#64) ∗ ((mp + 24#64) ↦₆₄ 0#64) ∗
    ((mp + 32#64) ↦₆₄ k0) ∗ ((mp + 32#64 + 8#64) ↦₆₄ k1) = _
  rw [hadd]

theorem protocolAddressAt_eq_vecGhostAt_parts (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64) :
    protocolAddressAt A g addr =
      vecGhostAt A g.name addr ∗ ((addr + 24#64) ↦₈ g.device) ∗ memRegion (addr + 25#64) 7 := rfl

theorem vecU8_and_dev_entails_protocolAddressAt_save (A : RustAlloc) (sp : BitVec 64)
    (bs : List (BitVec 8)) (dev : BitVec 8) :
    (vecU8 A (sp - 176#64) bs ∗ ((sp - 152#64) ↦₈ dev) ∗ memRegion (sp - 151#64) 7) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        protocolAddressAt A ⟨⟨cap, ptr, bs⟩, dev⟩ (sp - 176#64) := by
  unfold vecU8; simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap; apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e24 : sp - 176#64 + 24#64 = sp - 152#64 := by bv_omega
  have e25 : sp - 176#64 + 25#64 = sp - 151#64 := by bv_omega
  unfold protocolAddressAt vecGhostAt; rw [e24, e25]; exact Entails.of_eq (by ac_rfl)

theorem slot64_restore_parts (sp : BitVec 64) :
    memRegion (sp - 176#64) 32 ⊢
      ∃∗ c_sp88 : BitVec 8,
        memRegion (sp - 176#64) 24 ∗ ((sp - 152#64) ↦₈ c_sp88) ∗ memRegion (sp - 151#64) 7 := by
  rw [ProofLib.memRegion_split' (b := sp - 176#64) (n := 24) (k := 8) (b' := sp - 152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 152#64) (n := 1) (k := 7) (b' := sp - 151#64) rfl (by bv_omega) (by decide),
      memRegion_one (sp - 152#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; exact Entails.of_eq (by ac_rfl)

theorem optIdentityKeyAt_none_entails_memRegion33 (a : BitVec 64) :
    optIdentityKeyAt a none ⊢ memRegion a 33 := by
  unfold optIdentityKeyAt; rw [show (33 : Nat) = 1 + 32 from rfl, memRegion_split a 1 32 (by decide)]
  exact sepConj_mono_left (pointsTo8_entails_memRegion a 0#8)

theorem optIdentityKeyAt_some_entails_memRegion33 (a : BitVec 64) (bs : List (BitVec 8)) :
    optIdentityKeyAt a (some bs) ⊢ memRegion a 33 := by
  unfold optIdentityKeyAt; apply Entails.pure_left; intro hlen
  rw [show (33 : Nat) = 1 + 32 from rfl, memRegion_split a 1 32 (by decide)]
  exact sepConj_mono (pointsTo8_entails_memRegion a 1#8)
    (hlen ▸ pointsToBytes_entails_memRegion (a + 1#64) bs)

theorem pointsToBytes_32_eq_cells (a : BitVec 64) (bs : List (BitVec 8)) (hlen : bs.length = 32) :
    (a ↦ₛ bs) =
      (a ↦₆₄ loadGroupAt bs 0) ∗ ((a + 8#64) ↦₆₄ loadGroupAt bs 8) ∗
      ((a + 16#64) ↦₆₄ loadGroupAt bs 16) ∗ ((a + 24#64) ↦₆₄ loadGroupAt bs 24) := by
  have h0 : 0 + 8 ≤ bs.length := by omega
  have h8 : 8 + 8 ≤ bs.length := by omega
  have h16 : 16 + 8 ≤ bs.length := by omega
  have h24 : 24 + 8 ≤ bs.length := by omega
  rw [pointsToBytes_take_drop a 8 bs (by omega),
      pointsToBytes_take_drop (a + 8#64) 8 (bs.drop 8) (by simp [List.length_drop, hlen]), List.drop_drop,
      pointsToBytes_take_drop (a + 8#64 + 8#64) 8 (bs.drop 16) (by simp [List.length_drop, hlen]), List.drop_drop,
      pointsToBytes_take_drop (a + 8#64 + 8#64 + 8#64) 8 (bs.drop 24) (by simp [List.length_drop, hlen]), List.drop_drop]
  have hdrop32 : bs.drop 32 = [] := List.drop_eq_nil_of_le (by omega)
  have h0_eq := pointsToBytes_take8_eq_pointsTo64 a bs 0 h0
  simp only [List.drop_zero] at h0_eq
  have h8_eq := pointsToBytes_take8_eq_pointsTo64 (a + 8#64) bs 8 h8
  have h16_eq := pointsToBytes_take8_eq_pointsTo64 (a + 16#64) bs 16 h16
  have h24_eq := pointsToBytes_take8_eq_pointsTo64 (a + 24#64) bs 24 h24
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  simp only [Nat.reduceAdd, ha16, ha24, hdrop32, pointsToBytes_nil, sepConj_emp]
  rw [h0_eq, h8_eq, h16_eq, h24_eq, ← loadGroupAt_eq_pack64 bs 0 h0,
      ← loadGroupAt_eq_pack64 bs 8 h8, ← loadGroupAt_eq_pack64 bs 16 h16,
      ← loadGroupAt_eq_pack64 bs 24 h24]

theorem slot96_32_eq_bytes (sp : BitVec 64) (bs : List (BitVec 8)) (hlen : bs.length = 32) :
    (((sp - 144#64) ↦₆₄ loadGroupAt bs 0) ∗ ((sp - 136#64) ↦₆₄ loadGroupAt bs 8) ∗
      ((sp - 128#64) ↦₆₄ loadGroupAt bs 16) ∗ ((sp - 120#64) ↦₆₄ loadGroupAt bs 24)) =
    ((sp - 144#64) ↦ₛ bs) := by
  rw [pointsToBytes_32_eq_cells (sp - 144#64) bs hlen]
  have e1 : sp - 144#64 + 8#64 = sp - 136#64 := by bv_omega
  have e2 : sp - 144#64 + 16#64 = sp - 128#64 := by bv_omega
  have e3 : sp - 144#64 + 24#64 = sp - 120#64 := by bv_omega
  rw [e1, e2, e3]

@[arm64_norm, wp_norm]
theorem extractLsb'_0_64_append (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by
  ext i hi_lt; simp

@[arm64_norm, wp_norm]
theorem extractLsb'_64_64_append (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by
  ext i hi_lt; simp

theorem trace_eq_of_eq {s0 s sf : Arm64.State} (hs : s.trace = s0.trace)
    (h : allocFailedIn s sf ∧ s.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢; rw [← hs]; exact h

theorem wpp_call_stringClone_save {prog : Program} {entry ret_pc ret : BitVec 64}
    {A : RustAlloc} {s0 s : Arm64.State} {P F : SepProp}
    {Q : Arm64.State → SepProp → Prop} {Fr : SepProp}
    (p out sp' : BitVec 64) (g : VecGhost)
    (hcall : subroutine_ok prog entry (stringCloneSpec A))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = p) (hx8 : s.readReg64 .x8 = out)
    (hsp_eq : s.sp = sp') (htr : s.trace = s0.trace)
    (hP : P = (vecGhostAt A g p ∗ memRegion out 24 ∗ A.pool ∗ stackAt sp' extHookStack) ∗ F)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp' → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp prog ret sf
        (vecGhostAt A g p ∗ vecU8 A out g.bytes ∗ A.pool ∗ stackAt sp' extHookStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  refine SepWPp.call_frame (x := (p, out, g))
    (φ := s.readReg64 .x0 = p ∧ s.readReg64 .x8 = out)
    (T := vecGhostAt A g p ∗ memRegion out 24 ∗ A.pool ∗ stackAt sp' extHookStack)
    hcall hpc hrun hsp hlr (by dsimp only [stringCloneSpec]; rw [hsp_eq]) ⟨hx0, hx8⟩ hP
    (fun _ _ _ _ he => allowPanic_not_exited he)
    (fun sf _ hm => allowPanic_frame (trace_eq_of_eq htr) hm)
    fun sf hpcf hrunf hspf hcsf => ?_
  dsimp only [stringCloneSpec]; rw [hsp_eq, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_f => ?_
  conv => arg 4; simp only [sepConj_assoc]
  exact hnext sf hpcf hrunf (hspf.trans hsp_eq) hcsf (htr_f.trans htr)

theorem wpp_call_hashMapIdInsertEmpty {prog : Program} {entry ret_pc ret : BitVec 64}
    {A : RustAlloc} {s0 s : Arm64.State} {P F : SepProp}
    {Q : Arm64.State → SepProp → Prop} {Fr : SepProp}
    (sret base mp kPtr vPtr k0 k1 sp' : BitVec 64) (g : AddrGhost) (keyBytes : List (BitVec 8))
    (hcall : subroutine_ok prog entry (hashMapIdInsertEmptySpec A))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = sret) (hx1 : s.readReg64 .x1 = mp)
    (hx2 : s.readReg64 .x2 = kPtr) (hx3 : s.readReg64 .x3 = vPtr)
    (hname_len : g.name.bytes.length = 36) (hkey_len : keyBytes.length = 32)
    (hsp_eq : s.sp = sp') (htr : s.trace = s0.trace)
    (hP : P = (emptyTableAt base mp k0 k1 ∗ protocolAddressAt A g kPtr ∗
      (vPtr ↦ₛ keyBytes) ∗ memRegion sret 33 ∗ A.pool ∗ stackAt sp' hashMapIdInsertStack) ∗ F)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp' → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp prog ret sf
        (table4SingleAt A identityBucketStride mp k0 k1
            (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat
            g.name.bytes g.device (identityBucketEntryAt A g keyBytes) ∗
          memRegion kPtr 32 ∗ (vPtr ↦ₛ keyBytes) ∗ optIdentityKeyAt sret none ∗
          A.pool ∗ stackAt sp' hashMapIdInsertStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  refine SepWPp.call_frame (x := ⟨sret, base, mp, kPtr, vPtr, k0, k1, g, keyBytes⟩)
    (φ := s.readReg64 .x0 = sret ∧ s.readReg64 .x1 = mp ∧
      s.readReg64 .x2 = kPtr ∧ s.readReg64 .x3 = vPtr ∧
      g.name.bytes.length = 36 ∧ keyBytes.length = 32)
    (T := emptyTableAt base mp k0 k1 ∗ protocolAddressAt A g kPtr ∗
      (vPtr ↦ₛ keyBytes) ∗ memRegion sret 33 ∗ A.pool ∗ stackAt sp' hashMapIdInsertStack)
    hcall hpc hrun hsp hlr (by dsimp only [hashMapIdInsertEmptySpec]; rw [hsp_eq])
    ⟨hx0, hx1, hx2, hx3, hname_len, hkey_len⟩ hP
    (fun _ _ _ _ he => allowPanic_not_exited he)
    (fun sf _ hm => allowPanic_frame (trace_eq_of_eq htr) hm)
    fun sf hpcf hrunf hspf hcsf => ?_
  dsimp only [hashMapIdInsertEmptySpec]; rw [hsp_eq, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_f => ?_
  conv => arg 4; simp only [sepConj_assoc]
  exact hnext sf hpcf hrunf (hspf.trans hsp_eq) hcsf (htr_f.trans htr)

theorem hashMapIdInsert_fnAddr_of_save (b : BitVec 64) (ext : HookMap) :
    (RebasedProg b ext).fnAddr hashMapIdInsertName =
      (RebasedProg b ext).fnAddr saveIdentityClosureName + bv% (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") :=
  Program.fnAddr_rel saveIdentityClosure_fnOff hashMapIdInsert_fnOff (by decide)

theorem step_ldpSimd64_sp' {prog : Program} {target_pc : BitVec 64}
    {s s' : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {off ea ea2 v1 v2 : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .D64 vt1 vt2 (.Offset .sp off)))
    (hsp : checkRegSPAligned s .sp = true) (hea : s.sp + off = ea) (hea2 : ea + 8#64 = ea2)
    (hload1 : SepLoad64 ea P v1) (hload2 : SepLoad64 ea2 P v2)
    (hexec : (((s.writeVReg128 vt1 (v1.zeroExtend 128)).writeVReg128 vt2 (v2.zeroExtend 128)).setPC (pc + 4#64)) = s')
    (hnext : SepWP prog target_pc s' P post) : SepWP prog target_pc s P post :=
  step_ldpSimd64 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, AddrMode.baseReg, hsp])
    (by simp [evalAddrMode, Arm64.State.readReg64, hea])
    hea2 hload1 hload2 hexec hnext

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_pre (s : Arm64.State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem pc_setMem_pre (s : Arm64.State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem status_setMem_pre (s : Arm64.State) (m : Memory) : (s.setMem m).status = s.status := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_pre (s : Arm64.State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem spAligned_setMem_pre (s : Arm64.State) (m : Memory) :
    (s.setMem m).spAligned = s.spAligned := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem spAligned_setPC_pre (s : Arm64.State) (pc : BitVec 64) :
    (s.setPC pc).spAligned = s.spAligned := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_setPC_pre (s : Arm64.State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_setMem_pre (s : Arm64.State) (m : Memory) :
    (s.setMem m).trace = s.trace := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeReg64_pre (s : Arm64.State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).trace = s.trace := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeReg32_pre (s : Arm64.State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeVReg128_pre (s : Arm64.State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).trace = s.trace := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_setPState_pre (s : Arm64.State) (ps : PState) :
    (s.setPState ps).trace = s.trace := by cases s; rfl

theorem pollIdentityChangeResultAt_false_of_parts (sret : BitVec 64) :
    ((sret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sret + 8#64) ↦₃₂ 0#32) ∗
      memRegion (sret + 12#64) 36) ⊢ pollIdentityChangeResultAt sret false := Entails.refl _

theorem pollIdentityChangeResultAt_true_of_parts (sret : BitVec 64) :
    ((sret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sret + 8#64) ↦₃₂ 1#32) ∗
      memRegion (sret + 12#64) 36) ⊢ pollIdentityChangeResultAt sret true := Entails.refl _

set_option maxHeartbeats 800000 in
theorem saveIdentityEmpty_ok'_of_insert (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext)
    (hInsert0 : subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashMapIdInsertName)
      (hashMapIdInsertEmptySpec A)) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr saveIdentityClosureName)
      (saveIdentityEmptySpec A) := by
  have hClone := stringClone_ok_at_saveIdentity b hHooks
  have hInsert : subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr saveIdentityClosureName + bv% (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      (hashMapIdInsertEmptySpec A) := by
    rw [← hashMapIdInsert_fnAddr_of_save]
    exact hInsert0
  simp only [saveIdentityEmptySpec]
  have hfn : libsignalSessionCode.fnOff saveIdentityClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") :=
    saveIdentityClosure_fnOff
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")) 504
  clear hfn hHooks hInsert0
  dsimp only [RebasedProg, BitVec.ofNat_eq_ofNat] at hClone hInsert ⊢
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr saveIdentityClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨futPtr, sret, base, mp, k0, k1, qAddrPtr, qG, qKeyPtr, qKeyBytes⟩ := x
  dsimp only [SaveIdentityEmptyGhost.futPtr, SaveIdentityEmptyGhost.sret,
    SaveIdentityEmptyGhost.base, SaveIdentityEmptyGhost.mp,
    SaveIdentityEmptyGhost.k0, SaveIdentityEmptyGhost.k1,
    SaveIdentityEmptyGhost.qAddrPtr, SaveIdentityEmptyGhost.qKeyPtr,
    SaveIdentityEmptyGhost.qG, SaveIdentityEmptyGhost.qKeyBytes] at *
  conv =>
    arg 4
    rw [emptyTableAt_eq base mp k0 k1,
        pointsToBytes_32_eq_cells qKeyPtr qKeyBytes (by assumption),
        protocolAddressAt_eq_vecGhostAt_parts A qG qAddrPtr,
        sret48_save_split_eq sret,
        stackAt_save_eq s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply SepWPp.exists_elim; intro _)
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  conv =>
    arg 4
    rw [stackAt_save_ext_eq s0.sp]
    simp only [sepConj_assoc]
  refine wpp_call_stringClone_save (ret_pc := entry + bv% (392))
    qAddrPtr (s0.sp - 176#64) (s0.sp - 240#64) qG.name hClone
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal)
    (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
    (by simp only [wp_norm, arm64_norm, *])
    (by sep_focus) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  refine SepWPp.fold (Entails.of_eq (stackAt_save_ext_eq s0.sp).symm) (by sep_focus) ?_
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.fold (vecU8_and_dev_entails_protocolAddressAt_save A s0.sp qG.name.bytes qG.device)
    (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left]
  apply SepWPp.exists_elim; intro cap_c
  apply SepWPp.exists_elim; intro ptr_c
  refine SepWPp.fold (Entails.of_eq (slot96_32_eq_bytes s0.sp qKeyBytes (by assumption)))
    (by sep_focus) ?_
  refine SepWPp.fold (Entails.of_eq (emptyTableAt_eq base mp k0 k1).symm)
    (by sep_focus) ?_
  conv =>
    arg 4
    rw [stackAt_save_insert_eq s0.sp]
    simp only [sepConj_assoc]
  refine wpp_call_hashMapIdInsertEmpty (ret_pc := entry + bv% (432))
    (s0.sp - 209#64) base mp (s0.sp - 176#64) (s0.sp - 144#64)
    k0 k1 (s0.sp - 240#64) ⟨⟨cap_c, ptr_c, qG.name.bytes⟩, qG.device⟩ qKeyBytes hInsert
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal)
    (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
    (by assumption) (by assumption) (by wp_norm_goal)
    (by simp only [wp_norm, arm64_norm, *])
    (by sep_focus) ?_
  intro sf2 hpc2 hrun2 hsp2 hcs2 htr2
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  refine SepWPp.fold (Entails.of_eq (stackAt_save_insert_eq s0.sp).symm) (by sep_focus) ?_
  refine SepWPp.fold (optIdentityKeyAt_none_entails_memRegion33 (s0.sp - 209#64)) (by sep_focus) ?_
  refine SepWPp.fold (slot64_restore_parts s0.sp) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left]
  apply SepWPp.exists_elim; intro c_sp88_2
  refine SepWPp.fold (Entails.of_eq (slot96_32_eq_bytes s0.sp qKeyBytes (by assumption)).symm)
    (by sep_focus) ?_
  refine SepWPp.fold (Entails.of_eq (pointsToBytes_32_eq_cells qKeyPtr qKeyBytes (by assumption)).symm)
    (by sep_focus) ?_
  refine SepWPp.fold (Entails.of_eq (protocolAddressAt_eq_vecGhostAt_parts A qG qAddrPtr).symm)
    (by sep_focus) ?_
  apply SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.fold (pollIdentityChangeResultAt_false_of_parts sret) (by sep_focus) ?_
  refine SepWP.fold (stackAt_save_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  have hex_post :
      table4SingleAt A identityBucketStride mp k0 k1
        (hashAddrBv k0 k1 qG.name.bytes qG.device &&& 3#64).toNat
        qG.name.bytes qG.device
        (identityBucketEntryAt A ⟨⟨cap_c, ptr_c, qG.name.bytes⟩, qG.device⟩ qKeyBytes) ⊢
      ∃∗ cap_c : BitVec 64, ∃∗ ptr_c : BitVec 64,
        table4SingleAt A identityBucketStride mp k0 k1
          (hashAddrBv k0 k1 qG.name.bytes qG.device &&& 3#64).toNat
          qG.name.bytes qG.device
          (identityBucketEntryAt A ⟨⟨cap_c, ptr_c, qG.name.bytes⟩, qG.device⟩ qKeyBytes) :=
    entails_sepExists_intro cap_c (entails_sepExists_intro ptr_c (Entails.refl _))
  refine SepWP.fold hex_post (by sep_focus) ?_
  wp_done

/-! ## Helpers for `saveIdentitySingleHit_ok'_of_insert` -/

theorem sepWPp_extract_pure {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : Prop} {Q F : SepProp} {post postP : Arm64.State → SepProp → Prop}
    (heq : Q = ⌜P⌝ ∗ F)
    (h : P → SepWPp prog pc s F post postP) :
    SepWPp prog pc s Q post postP := by
  rw [heq]
  exact SepWPp.pure_elim h

theorem stackAt_save_ext_restore (sp sp' : BitVec 64)
    (h : sp' = bv% (2 ^ 64 - 240) + sp) :
    memRegion (sp - 17184#64) 560 ∗ stackAt sp' extHookStack ⊢
      memRegion (sp - 17184#64) 16944 := by
  have hsp : sp' = sp - 240#64 := by rw [h]; bv_omega
  rw [hsp, ← stackAt_save_ext_eq sp]
  exact Entails.refl _

theorem stackAt_save_insert_restore (sp sp' : BitVec 64)
    (h : sp' = sp - 240#64) :
    memRegion (sp - 17184#64) 16 ∗ stackAt sp' hashMapIdInsertStack ⊢
      memRegion (sp - 17184#64) 16944 := by
  rw [h, ← stackAt_save_insert_eq sp]
  exact Entails.refl _

theorem table4SingleAt_eq (A : RustAlloc) (stride : Nat) (mp k0 k1 : BitVec 64)
    (k : Nat) (peerName : List (BitVec 8)) (peerDev : BitVec 8)
    (entryAt : BitVec 64 → SepProp) :
    table4SingleAt A stride mp k0 k1 k peerName peerDev entryAt =
      ⌜k < 4⌝ ∗
      ∃∗ ctrl : BitVec 64,
        ⌜ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧
          4 * stride ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64 ∧
          ([k].length = 4 → 2#64 = 0#64) ∧
          CtrlMirrorInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∧
          FullBucketsInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) [k]⌝ ∗
        (mp ↦₆₄ ctrl) ∗ ((mp + 8#64) ↦₆₄ 3#64) ∗ ((mp + 16#64) ↦₆₄ 2#64) ∗ ((mp + 24#64) ↦₆₄ 1#64) ∗
        ((mp + 32#64) ↦₆₄ k0) ∗ ((mp + 40#64) ↦₆₄ k1) ∗
        A.live (ctrl - BitVec.ofNat 64 (4 * stride)) (tableAllocSize 4 stride) 8 ∗
        (ctrl ↦ₛ singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∗
        arrayAt
          (fun i a => if i ∈ [k] then entryAt a else memRegion a stride) stride
          (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse := by
  have hadd : mp + 32#64 + 8#64 = mp + 40#64 := by bv_omega
  dsimp only [table4SingleAt, table4At]
  simp only [hadd]
  rfl

theorem table4SingleAt_of_parts (A : RustAlloc) (stride : Nat) (mp k0 k1 : BitVec 64)
    (k : Nat) (hk : k < 4) (peerName : List (BitVec 8)) (peerDev : BitVec 8)
    (entryAt : BitVec 64 → SepProp) (ctrl : BitVec 64)
    (hctrl : ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧
      4 * stride ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64 ∧
      ([k].length = 4 → 2#64 = 0#64) ∧
      CtrlMirrorInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∧
      FullBucketsInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) [k]) :
    ((mp ↦₆₄ ctrl) ∗ ((mp + 8#64) ↦₆₄ 3#64) ∗ ((mp + 16#64) ↦₆₄ 2#64) ∗ ((mp + 24#64) ↦₆₄ 1#64) ∗
      ((mp + 32#64) ↦₆₄ k0) ∗ ((mp + 40#64) ↦₆₄ k1) ∗
      A.live (ctrl - BitVec.ofNat 64 (4 * stride)) (tableAllocSize 4 stride) 8 ∗
      (ctrl ↦ₛ singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∗
      arrayAt
        (fun i a => if i ∈ [k] then entryAt a else memRegion a stride) stride
        (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse) ⊢
    table4SingleAt A stride mp k0 k1 k peerName peerDev entryAt := by
  rw [table4SingleAt_eq]
  apply Entails.pure_right hk
  refine entails_sepExists_intro ctrl ?_
  exact Entails.pure_right hctrl (Entails.refl _)

def addrRestAt (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64) : SepProp :=
  ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
  (addr ↦₆₄ g.name.cap) ∗
  A.live g.name.ptr g.name.cap.toNat 1 ∗
  memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
    (g.name.cap.toNat - g.name.bytes.length) ∗
  memRegion (addr + 25#64) 7

theorem protocolAddressAt_eq_of_len36 (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64)
    (hlen36 : g.name.bytes.length = 36) :
    protocolAddressAt A g addr =
      ((addr + 8#64) ↦₆₄ g.name.ptr) ∗ ((addr + 16#64) ↦₆₄ 36#64) ∗
      ((addr + 24#64) ↦₈ g.device) ∗ (g.name.ptr ↦ₛ g.name.bytes) ∗
      addrRestAt A g addr := by
  have hvec :
      vecGhostAt A g.name addr =
        ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        (addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗ ((addr + 16#64) ↦₆₄ 36#64) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
        memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
          (g.name.cap.toNat - g.name.bytes.length) := by
    unfold vecGhostAt vecU8At vecHeader
    have h1 :
        ((addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
            (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          if g.name.cap = 0 then emp
          else A.live g.name.ptr g.name.cap.toNat 1 ∗ g.name.ptr ↦ₛ g.name.bytes ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) ⊢
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗ (addr + 16#64) ↦₆₄ 36#64 ∗
          g.name.ptr ↦ₛ g.name.bytes ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length)) := by
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
      have hne : g.name.cap ≠ 0 := by
        intro h0; rw [h0] at hlen; change g.name.bytes.length ≤ 0 at hlen; omega
      simp only [hne, ↓reduceIte, hlen36] at hlen ⊢
      apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
      exact Entails.of_eq (by ac_rfl)
    have h2 :
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗ (addr + 16#64) ↦₆₄ 36#64 ∗
          g.name.ptr ↦ₛ g.name.bytes ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length)) ⊢
        ((addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
            (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          if g.name.cap = 0 then emp
          else A.live g.name.ptr g.name.cap.toNat 1 ∗ g.name.ptr ↦ₛ g.name.bytes ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) := by
      apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
      have hne : g.name.cap ≠ 0 := by
        intro h0; rw [h0] at hlen; change g.name.bytes.length ≤ 0 at hlen; omega
      rw [sepConj_pure_left_comm]
      apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
      simp only [hne, ↓reduceIte, hlen36]
      exact Entails.of_eq (by ac_rfl)
    exact ProofLib.sepProp_eq_of_entails h1 h2
  unfold protocolAddressAt addrRestAt
  rw [hvec]
  ac_rfl

theorem sub_shl6_eq_bucketAddr_add_64 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    ctrl - (BitVec.ofNat 64 k <<< 6) = bucketAddr ctrl 64 k + 64#64 := by
  unfold bucketAddr
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> bv_omega

theorem bucketArray_save_eq (A : RustAlloc) (ctrl : BitVec 64) (k : Nat)
    (peerG : AddrGhost) (peerKeyBytes : List (BitVec 8))
    (hk : k < 4) (hlen_name : peerG.name.bytes.length = 36) (hlen_key : peerKeyBytes.length = 32) :
    arrayAt
      (fun i a => if i ∈ [k] then identityBucketEntryAt A peerG peerKeyBytes a else memRegion a identityBucketStride)
      identityBucketStride (ctrl - BitVec.ofNat 64 (4 * identityBucketStride)) (List.range 4).reverse =
    ((bucketAddr ctrl 64 k + 8#64) ↦₆₄ peerG.name.ptr) ∗
    ((bucketAddr ctrl 64 k + 16#64) ↦₆₄ 36#64) ∗
    ((bucketAddr ctrl 64 k + 24#64) ↦₈ peerG.device) ∗
    (peerG.name.ptr ↦ₛ peerG.name.bytes) ∗
    ((bucketAddr ctrl 64 k + 32#64) ↦ₛ peerKeyBytes) ∗
    addrRestAt A peerG (bucketAddr ctrl 64 k) ∗
    singleBucketRestAt 64 ctrl k := by
  change arrayAt
    (fun i a => if i ∈ [k] then identityBucketEntryAt A peerG peerKeyBytes a else memRegion a 64)
    64 (ctrl - BitVec.ofNat 64 (4 * 64)) (List.range 4).reverse = _
  rw [arrayAt_single_split_64 ctrl k hk (identityBucketEntryAt A peerG peerKeyBytes)]
  unfold identityBucketEntryAt
  rw [protocolAddressAt_eq_of_len36 A peerG (bucketAddr ctrl 64 k) hlen_name]
  simp only [hlen_key, pure_true, emp_sepConj]
  ac_rfl

private theorem memRegion_16_eq_stackFrameFor_eq (sp : BitVec 64) :
    memRegion (sp - 16#64) 16 =
      stackFrameFor libsignalSessionImage
        "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp := by
  rw [show (16 : Nat) = 8 * 2 by rfl, memRegion_cells (sp - 16#64) 2 (by decide)]
  cells_unfold
  simp only [stackFrameFor, libsignalSessionCode_frameBytes_0x3ecd4, reduceStackFrameAt]

private theorem memRegion_48_eq_stackFrameFor_ct_eq (sp : BitVec 64) :
    memRegion (sp - 48#64) 48 =
      stackFrameFor libsignalSessionImage
        "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp := by
  rw [show (48 : Nat) = 8 * 6 by rfl, memRegion_cells (sp - 48#64) 6 (by decide)]
  cells_unfold
  simp only [stackFrameFor, libsignalSessionCode_frameBytes_0x3eda8, reduceStackFrameAt]

private theorem stackAt_extHookStack_split_publicKeyEq (sp : BitVec 64) :
    stackAt sp extHookStack =
      memRegion (sp - 16384#64) 16320 ∗ memRegion (sp - 16#64) 16 ∗ memRegion (sp - 16#64 - 48#64) 48 := by
  simp only [stackAt, HashbrownBin.extHookStack]
  have h64 : sp - 16#64 - 48#64 = sp - 64#64 := by bv_omega
  rw [h64, show BitVec.ofNat 64 (2 ^ 14) = 16384#64 from rfl, show (2 ^ 14 : Nat) = 16384 from rfl,
      ProofLib.memRegion_split' (b := sp - 16384#64) (n := 16320) (k := 64) (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 48) (k := 16) (b' := sp - 16#64) rfl (by bv_omega) (by decide)]
  ac_rfl

structure PublicKeyEqSliceCall where
  p1 : BitVec 64
  bs1 : List (BitVec 8)
  p2 : BitVec 64
  bs2 : List (BitVec 8)
  sp : BitVec 64

def publicKeyEqSliceSpec : Spec PublicKeyEqSliceCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p1 ∧ s.readReg64 .x1 = x.p2 ∧ s.sp = x.sp ∧
      x.bs1.length = 32 ∧ x.bs2.length = 32⌝ ∗
    (x.p1 ↦ₛ x.bs1) ∗ (x.p2 ↦ₛ x.bs2) ∗ stackAt x.sp extHookStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = (if x.bs1 = x.bs2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (x.p1 ↦ₛ x.bs1) ∗ (x.p2 ↦ₛ x.bs2) ∗ stackAt x.sp extHookStack

theorem publicKeyEqSlice_ok_at_saveIdentity (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr saveIdentityClosureName + bv% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      publicKeyEqSliceSpec := by
  refine subroutine_ok_map (publicKeyEq_ok_at_saveIdentity b hHooks) ?_
  rintro ⟨p1, bs1, p2, bs2, sp⟩ R s0 hpre
  simp only [publicKeyEqSliceSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hsp, hlen1, hlen2⟩, hmem⟩
  let pk1 : PublicKey := ⟨⟨bs1, hlen1⟩⟩
  let pk2 : PublicKey := ⟨⟨bs2, hlen2⟩⟩
  have hpk1 : pk1.bytes.toList = bs1 := rfl
  have hpk2 : pk2.bytes.toList = bs2 := rfl
  rw [stackAt_extHookStack_split_publicKeyEq sp] at hmem
  refine ⟨(p1, pk1, p2, pk2, sp), memRegion (sp - 16384#64) 16320 ∗ R, ?_, fun sf hpost => ?_⟩
  · simp only [CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqSpec,
      ← memRegion_16_eq_stackFrameFor_eq sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq (sp - 16#64),
      hpk1, hpk2, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hsp⟩, ?_⟩
    convert hmem using 1; ac_rfl
  · simp only [CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqSpec,
      ← memRegion_16_eq_stackFrameFor_eq sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq (sp - 16#64),
      hpk1, hpk2, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hret, htr⟩, hpost⟩
    rw [← CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_ite_toList_eq pk1 pk2] at hret
    change sf.readReg64 .x0 = (if bs1 = bs2 then 1#64 else 0#64) at hret
    simp only [publicKeyEqSliceSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hret, htr⟩, ?_⟩
    rw [stackAt_extHookStack_split_publicKeyEq sp]
    convert hpost using 1; ac_rfl

private theorem zext128_shr_and_255_eq_groupByte (w : BitVec 64) (i : Nat) :
    BitVec.zeroExtend 128 w >>> (i * 8) &&& 255#128 = (groupByte w i).zeroExtend 128 := by
  apply BitVec.eq_of_toNat_eq
  have hw : w.toNat < 2 ^ 64 := w.isLt
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, groupByte, BitVec.toNat_setWidth]
  change ((w.toNat % 2 ^ 128) >>> (i * 8)) &&& (2 ^ 8 - 1) = ((w.toNat >>> (8 * i)) % 256) % 2 ^ 128
  have hmod1 : w.toNat % 2 ^ 128 = w.toNat := Nat.mod_eq_of_lt (by omega)
  have hmod2 : (w.toNat >>> (8 * i)) % 256 % 2 ^ 128 = (w.toNat >>> (8 * i)) % 256 := Nat.mod_eq_of_lt (by omega)
  rw [hmod1, hmod2, Nat.and_two_pow_sub_one_eq_mod, Nat.mul_comm i 8]

private theorem zext128_shr57_and_255_eq_h2Tag (h : BitVec 64) :
    BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 = (h2Tag h).zeroExtend 128 := by
  apply BitVec.eq_of_toNat_eq
  have hh : (h >>> 57).toNat < 128 := by rw [BitVec.toNat_ushiftRight]; have := h.isLt; omega
  rw [BitVec.toNat_and, BitVec.toNat_setWidth, h2Tag, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth]
  change ((h >>> 57).toNat % 2 ^ 128) &&& (2 ^ 8 - 1) = (((h >>> 57).toNat % 256) &&& (2 ^ 7 - 1)) % 2 ^ 128
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]; omega

private abbrev dupTag128 (qtag : BitVec 8) : BitVec 128 :=
  0#128 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 0 ||| (qtag.zeroExtend 128 &&& 255#128) <<< 8 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 16 ||| (qtag.zeroExtend 128 &&& 255#128) <<< 24 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 32 ||| (qtag.zeroExtend 128 &&& 255#128) <<< 40 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 48 ||| (qtag.zeroExtend 128 &&& 255#128) <<< 56

private theorem dupTag128_lane_0 (qtag : BitVec 8) : dupTag128 qtag >>> 0 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_8 (qtag : BitVec 8) : dupTag128 qtag >>> 8 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_16 (qtag : BitVec 8) : dupTag128 qtag >>> 16 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_24 (qtag : BitVec 8) : dupTag128 qtag >>> 24 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_32 (qtag : BitVec 8) : dupTag128 qtag >>> 32 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_40 (qtag : BitVec 8) : dupTag128 qtag >>> 40 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_48 (qtag : BitVec 8) : dupTag128 qtag >>> 48 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_56 (qtag : BitVec 8) : dupTag128 qtag >>> 56 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel

private theorem beq_zext128_eq (a b : BitVec 8) :
    (a.zeroExtend 128 == b.zeroExtend 128) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : a.zeroExtend 128 ≠ b.zeroExtend 128 := by
      intro heq; apply h; apply BitVec.eq_of_toNat_eq
      have hnat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth] at hnat
      have := a.isLt; have := b.isLt; omega
    simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr hne]

private theorem truncate64_or (x y : BitVec 128) :
    BitVec.truncate 64 (x ||| y) = BitVec.truncate 64 x ||| BitVec.truncate 64 y := BitVec.setWidth_or

private theorem truncate64_cmeq_0 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 0) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 := by cases c <;> rfl
private theorem truncate64_cmeq_8 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 8) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 8 := by cases c <;> rfl
private theorem truncate64_cmeq_16 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 16) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 16 := by cases c <;> rfl
private theorem truncate64_cmeq_24 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 24) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 24 := by cases c <;> rfl
private theorem truncate64_cmeq_32 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 32) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 32 := by cases c <;> rfl
private theorem truncate64_cmeq_40 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 40) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 40 := by cases c <;> rfl
private theorem truncate64_cmeq_48 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 48) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 48 := by cases c <;> rfl
private theorem truncate64_cmeq_56 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 56) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 56 := by cases c <;> rfl

theorem rawMatchTagMask_eq_findGroupIterMask (cbs : List (BitVec 8)) (pos : Nat) (h : BitVec 64) :
    BitVec.truncate 64
      (0#128 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 0 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 0 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 0 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 8 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 8 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 8 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 16 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 16 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 16 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 24 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 24 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 24 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 32 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 32 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 32 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 40 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 40 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 40 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 48 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 48 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 48 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 56 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 56 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 56) &&&
      9259542123273814144#64 =
    findGroupIterMask cbs pos (h2Tag h) := by
  rw [zext128_shr57_and_255_eq_h2Tag h]
  change BitVec.truncate 64
      (0#128 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (0 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 0 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 0 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (1 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 8 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 8 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (2 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 16 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 16 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (3 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 24 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 24 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (4 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 32 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 32 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (5 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 40 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 40 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (6 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 48 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 48 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (7 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 56 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 56) &&&
      9259542123273814144#64 =
    findGroupIterMask cbs pos (h2Tag h)
  rw [zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 0,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 1,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 2,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 3,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 4,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 5,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 6,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 7,
      dupTag128_lane_0, dupTag128_lane_8, dupTag128_lane_16, dupTag128_lane_24,
      dupTag128_lane_32, dupTag128_lane_40, dupTag128_lane_48, dupTag128_lane_56]
  simp only [beq_zext128_eq, truncate64_or,
    truncate64_cmeq_0, truncate64_cmeq_8, truncate64_cmeq_16, truncate64_cmeq_24,
    truncate64_cmeq_32, truncate64_cmeq_40, truncate64_cmeq_48, truncate64_cmeq_56,
    BitVec.zero_or]
  rfl

theorem eval_probeBucket_singleCtrl4 (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    (BitVec.ofNat 64 pos +
      (laneBit (laneOfBucket4 pos k)).reverse.clz >>> 3) &&& 3#64 = BitVec.ofNat 64 k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> decide +kernel

theorem laneBit_laneOfBucket4_ne_zero (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    laneBit (laneOfBucket4 pos k) ≠ 0#64 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> decide +kernel

theorem findGroupIterMask_singleCtrl4_eq_zero_imp_ne
    (k0 k1 : BitVec 64) (k : Nat) (hk : k < 4)
    (peerName qName : List (BitVec 8)) (peerDev qDev : BitVec 8)
    (hmask0 : findGroupIterMask (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev)))
      (hashAddrBv k0 k1 qName qDev &&& 3#64).toNat (h2Tag (hashAddrBv k0 k1 qName qDev)) = 0#64) :
    ¬(qName = peerName ∧ qDev = peerDev) := by
  rintro ⟨rfl, rfl⟩
  have hpos : (hashAddrBv k0 k1 qName qDev &&& 3#64).toNat < 4 :=
    probePos_3_toNat_lt (hashAddrBv k0 k1 qName qDev)
  rw [findGroupIterMask_singleCtrl4 k _ hk hpos] at hmask0
  simp only [beq_self_eq_true, ↓reduceIte] at hmask0
  exact laneBit_laneOfBucket4_ne_zero k _ hk hpos hmask0

theorem findGroupIterMask_singleCtrl4_ne_zero_eq
    (k0 k1 : BitVec 64) (k pos : Nat) (hk : k < 4) (hpos : pos < 4)
    (peerName qName : List (BitVec 8)) (peerDev qDev : BitVec 8)
    (hmask_ne : ¬findGroupIterMask (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev)))
      pos (h2Tag (hashAddrBv k0 k1 qName qDev)) = 0#64) :
    findGroupIterMask (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev)))
      pos (h2Tag (hashAddrBv k0 k1 qName qDev)) = laneBit (laneOfBucket4 pos k) := by
  rw [findGroupIterMask_singleCtrl4 k pos hk hpos] at hmask_ne ⊢
  split at hmask_ne
  · rename_i heq; simp [heq]
  · exfalso; exact hmask_ne rfl

theorem ne_of_cbnz_bcmp {w : BitVec 32} {P Q : Prop}
    (hiff : (w = 0#32) ↔ P) (hcbnz : ¬BitVec.zeroExtend 64 w = 0#64) : ¬(P ∧ Q) := by
  intro ⟨hp, _⟩; apply hcbnz; have hw : w = 0#32 := hiff.mpr hp; subst hw; rfl

theorem dev_ne_of_not_zeroExtend {P : Prop} {d1 d2 : BitVec 8}
    (h : ¬BitVec.zeroExtend 64 d1 = BitVec.zeroExtend 64 d2) : ¬(P ∧ d1 = d2) := by
  rintro ⟨_, rfl⟩; exact h rfl

set_option maxHeartbeats 1200000 in
theorem saveIdentitySingleHit_ok'_of_insert (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext)
    (hInsert0 : subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashMapIdInsertName)
      (hashMapIdInsertSingleHitSpec A)) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr saveIdentityClosureName)
      (saveIdentitySingleHitSpec A) := by
  have hHash : subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr saveIdentityClosureName + 0xfffffffffffff5dc#64)
      (hashOneAddr36Spec A) := by
    have h := hashOneAddr36_ok_at_saveIdentityClosure b ext A
    have hsub : (RebasedProg b ext).fnAddr saveIdentityClosureName + 0xfffffffffffff5dc#64 =
        (SipHashBin.RebasedProg b ext).fnAddr SipHashBin.saveIdentityClosureName - 0x0a24#64 := by
      rw [BitVec.sub_eq_add_neg]; rfl
    rwa [hsub]
  have hBcmp := bcmp_ok_at_saveIdentity b hHooks
  have hPkEq := publicKeyEqSlice_ok_at_saveIdentity b hHooks
  have hClone := stringClone_ok_at_saveIdentity b hHooks
  have hInsert : subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr saveIdentityClosureName + bv% (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      (hashMapIdInsertSingleHitSpec A) := by
    rw [← hashMapIdInsert_fnAddr_of_save]; exact hInsert0
  simp only [saveIdentitySingleHitSpec]
  have hfn : libsignalSessionCode.fnOff saveIdentityClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") := saveIdentityClosure_fnOff
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")) 504
  clear hfn hHooks hInsert0
  dsimp only [RebasedProg, BitVec.ofNat_eq_ofNat] at hHash hBcmp hPkEq hClone hInsert ⊢
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr saveIdentityClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨futPtr, sret, mp, k0, k1, k, peerG, oldKeyBytes, qAddrPtr, qG, qKeyPtr, newKeyBytes⟩ := x
  dsimp only [SaveIdentitySingleHitGhost.futPtr, SaveIdentitySingleHitGhost.sret,
    SaveIdentitySingleHitGhost.mp, SaveIdentitySingleHitGhost.k0, SaveIdentitySingleHitGhost.k1,
    SaveIdentitySingleHitGhost.k, SaveIdentitySingleHitGhost.peerG,
    SaveIdentitySingleHitGhost.oldKeyBytes, SaveIdentitySingleHitGhost.qAddrPtr,
    SaveIdentitySingleHitGhost.qG, SaveIdentitySingleHitGhost.qKeyPtr,
    SaveIdentitySingleHitGhost.newKeyBytes] at *
  have hq_len : qG.name.bytes.length = 36 := by
    rw [‹qG.name.bytes = peerG.name.bytes›, ‹peerG.name.bytes.length = 36›]
  conv =>
    arg 4
    rw [table4SingleAt_eq A identityBucketStride mp k0 k1 k peerG.name.bytes peerG.device
          (identityBucketEntryAt A peerG oldKeyBytes)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro ctrl
  conv =>
    arg 4
    rw [sret48_save_split_eq sret, stackAt_save_eq s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply SepWPp.exists_elim; intro _)
  refine sepWPp_extract_pure (P := k < 4) (by sep_focus) fun hk => ?_
  refine sepWPp_extract_pure (by sep_focus) ?_
  rintro ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (308))
  wp_steps
  wp_conv_pre => rw [stackAt_save_hashOne_eq s0.sp]
  wp_apply
  refine SepWP.fold (Entails.of_eq (stackAt_save_hashOne_eq s0.sp).symm) (by sep_focus) ?_
  wp_conv_pre => rw [protocolAddressAt_eq_of_len36 A qG qAddrPtr hq_len]
  wp_steps
  let pos := (hashAddrBv k0 k1 peerG.name.bytes peerG.device &&& 3#64).toNat
  have hpos_lt : pos < 4 := probePos_3_toNat_lt (hashAddrBv k0 k1 peerG.name.bytes peerG.device)
  have hpos_bv : BitVec.ofNat 64 pos = hashAddrBv k0 k1 peerG.name.bytes peerG.device &&& 3#64 := by simp [pos]
  have hcbs_len : (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerG.name.bytes peerG.device))).length = 12 := by
    simp [singleCtrl4, mkCtrl4]
  have hcbs_split := pointsToBytes_ctrl12_split_at ctrl
    (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerG.name.bytes peerG.device))) hcbs_len pos hpos_lt
  rw [hpos_bv] at hcbs_split
  refine SepWP.fold (Entails.of_eq hcbs_split) (by sep_focus) ?_
  refine step_ldrSimd64 (ea := ctrl + (hashAddrBv k0 k1 peerG.name.bytes peerG.device &&& 3#64)) (wb := none)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_assumption)
    rfl (by simp [evalAddrMode, extendVal, arm64_norm, *])
    (by wp_sep_access_fast) (by wp_norm_lhs) ?_
  wp_conv_pre => rw [← hcbs_split]
  wp_steps
  conv => arg 3; rw [rawMatchTagMask_eq_findGroupIterMask]
  wp_if hmask
  · exfalso
    exact (findGroupIterMask_singleCtrl4_eq_zero_imp_ne k0 k1 k hk
      peerG.name.bytes peerG.name.bytes peerG.device peerG.device hmask)
      ⟨rfl, rfl⟩
  · have hmask_eq := findGroupIterMask_singleCtrl4_ne_zero_eq k0 k1 k pos hk hpos_lt
      peerG.name.bytes peerG.name.bytes peerG.device peerG.device hmask
    conv => arg 3; rw [hmask_eq]
    refine SepWP.fold (Entails.of_eq (bucketArray_save_eq A ctrl k peerG oldKeyBytes hk (by assumption) (by assumption)))
      (by sep_focus) ?_
    wp_steps
    conv =>
      arg 3
      rw [← hpos_bv, eval_probeBucket_singleCtrl4 k pos hk hpos_lt,
          sub_shl6_eq_bucketAddr_add_64 ctrl k hk]
    wp_steps
    wp_conv_pre => rw [stackAt_save_ext_eq s0.sp]
    wp_apply
    refine SepWP.fold (stackAt_save_ext_restore s0.sp _ (by assumption)) (by sep_focus) ?_
    wp_steps
    wp_if hcbnz
    · exfalso
      exact (ne_of_cbnz_bcmp (by assumption) hcbnz)
        ⟨‹qG.name.bytes = peerG.name.bytes›, ‹qG.device = peerG.device›⟩
    · clear hcbnz
      wp_steps
      wp_conv_pre => rw [stackAt_save_ext_eq s0.sp]
      wp_apply
      refine SepWP.fold (Entails.of_eq (stackAt_save_ext_eq s0.sp).symm) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A qG qAddrPtr hq_len).symm) (by sep_focus) ?_
      refine SepWPp.fold (Entails.of_eq (bucketArray_save_eq A ctrl k peerG oldKeyBytes hk (by assumption) (by assumption)).symm)
        (by sep_focus) ?_
      refine SepWPp.fold (table4SingleAt_of_parts A identityBucketStride mp k0 k1 k hk
        peerG.name.bytes peerG.device (identityBucketEntryAt A peerG oldKeyBytes) ctrl
        ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩) (by sep_focus) ?_
      by_cases hkey_eq : oldKeyBytes = newKeyBytes
      · subst hkey_eq
        simp only [↓reduceIte, ne_eq, not_true_eq_false, decide_false] at *
        apply SepWPp.of_sepWP_ret
        wp_steps
        refine SepWP.fold (pollIdentityChangeResultAt_false_of_parts sret) (by sep_focus) ?_
        refine SepWP.fold (stackAt_save_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
        wp_done
      · simp only [hkey_eq, ↓reduceIte, ne_eq, not_false_eq_true, decide_true] at *
        apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.fold (Entails.of_eq (protocolAddressAt_eq_vecGhostAt_parts A qG qAddrPtr)) (by sep_focus) ?_
        conv => arg 4; rw [stackAt_save_ext_eq s0.sp]; simp only [sepConj_assoc]
        refine wpp_call_stringClone_save (ret_pc := entry + bv% (328))
          qAddrPtr (s0.sp - 176#64) (s0.sp - 240#64) qG.name hClone
          (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal)
          (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, *]) (by sep_focus) ?_
        intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
        simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hcs1
        rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩
        refine SepWPp.fold (Entails.of_eq (stackAt_save_ext_eq s0.sp).symm) (by sep_focus) ?_
        apply SepWPp.of_sepWP_ret
        refine SepWP.fold (Entails.of_eq (pointsToBytes_32_eq_cells qKeyPtr newKeyBytes (by assumption))) (by sep_focus) ?_
        wp_steps
        refine SepWP.fold (vecU8_and_dev_entails_protocolAddressAt_save A s0.sp qG.name.bytes peerG.device) (by sep_focus) ?_
        wp_simp_pre [sepExists_sepConj_left]
        apply sepWP_exists_elim; intro cap_c; apply sepWP_exists_elim; intro ptr_c
        refine SepWP.fold (Entails.of_eq (slot96_32_eq_bytes s0.sp newKeyBytes (by assumption))) (by sep_focus) ?_
        wp_conv_pre => rw [stackAt_save_insert_eq s0.sp]
        wp_call hInsert ⟨s0.sp - 209#64, mp, s0.sp - 176#64, s0.sp - 144#64, k0, k1, k,
          peerG, ⟨⟨cap_c, ptr_c, qG.name.bytes⟩, peerG.device⟩, oldKeyBytes, newKeyBytes⟩
        refine SepWP.fold (stackAt_save_insert_restore s0.sp _ (by assumption)) (by sep_focus) ?_
        refine SepWP.fold (optIdentityKeyAt_some_entails_memRegion33 (s0.sp - 209#64) oldKeyBytes) (by sep_focus) ?_
        refine SepWP.fold (slot64_restore_parts s0.sp) (by sep_focus) ?_
        wp_simp_pre [sepExists_sepConj_left]
        apply sepWP_exists_elim; intro c_sp88_2
        refine SepWP.fold (Entails.of_eq (slot96_32_eq_bytes s0.sp newKeyBytes (by assumption)).symm) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (pointsToBytes_32_eq_cells qKeyPtr newKeyBytes (by assumption)).symm) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_vecGhostAt_parts A qG qAddrPtr).symm) (by sep_focus) ?_
        wp_steps
        refine SepWP.fold (pollIdentityChangeResultAt_true_of_parts sret) (by sep_focus) ?_
        refine SepWP.fold (stackAt_save_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
        wp_done

abbrev saveIdentityEmpty_ok' := @saveIdentityEmpty_ok'_of_insert
abbrev saveIdentitySingleHit_ok' := @saveIdentitySingleHit_ok'_of_insert

end SaveIdentity

export SaveIdentity (saveIdentityEmpty_ok'_of_insert saveIdentitySingleHit_ok'_of_insert
  saveIdentityEmpty_ok' saveIdentitySingleHit_ok')

end CryptoVerification.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures
