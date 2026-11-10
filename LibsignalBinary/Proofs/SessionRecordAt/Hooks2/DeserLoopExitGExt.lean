/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Adapters
import ProofLib.SepLogic.WPFrozen
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.DeserLoopExitG
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.WaveCTemplates
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionRecord::deserialize` Loop Exit (`+0x254` → `ret`)

Verifies the `SessionRecord::deserialize` loop exit when `rem = 0`, discharging the four struct-move
`memcpy` calls on `SP2Ext` and under relocatable `[LibsignalPlacement]`.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession)
open Proofs.libsignal.Hooks2 CryptoVerification.CodeLayout

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem DLEGX1 : True := trivial

/-! ## `prostSSGAt` move helpers -/

private def RelocAt_ssmove (k n : Nat) (P : BitVec 64 → SepProp) : Prop :=
  ∀ a : BitVec 64, P a ⊢
    ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
      ⌜bs.length = n ∧ ∀ b : BitVec 64, (((b + BitVec.ofNat 64 k) ↦ₛ bs) ∗ H) ⊢ P b⌝ ∗
      ((a + BitVec.ofNat 64 k) ↦ₛ bs) ∗ H

private theorem relocAt_congr_ssmove {k n : Nat} {P Q : BitVec 64 → SepProp}
    (heq : ∀ a, Q a = P a) (hP : RelocAt_ssmove k n P) : RelocAt_ssmove k n Q := by
  intro a
  rw [heq a]
  refine Entails.trans (hP a) ?_
  apply Entails.sepExists_elim; intro bs
  refine Entails.sepExists_right bs ?_
  apply Entails.sepExists_elim; intro H
  refine Entails.sepExists_right H ?_
  apply Entails.pure_left; rintro ⟨hlen, hrec⟩
  refine Entails.pure_right ⟨hlen, fun b => ?_⟩ (Entails.refl _)
  rw [heq b]
  exact hrec b

private theorem relocAt_pointsToBytes_ssmove (k : Nat) (off : BitVec 64) (bs : List (BitVec 8))
    {n : Nat} (hoff : off = BitVec.ofNat 64 k) (hn : bs.length = n) :
    RelocAt_ssmove k n (fun a => (a + off) ↦ₛ bs) := by
  subst hoff
  intro a
  refine Entails.sepExists_right bs (Entails.sepExists_right emp ?_)
  rw [sepConj_emp]
  refine Entails.pure_right ⟨hn, fun b => ?_⟩ (Entails.refl _)
  rw [sepConj_emp]
  exact Entails.refl _

private theorem relocAt_pointsTo32_ssmove (k : Nat) (off : BitVec 64) (w : BitVec 32)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_ssmove k 4 (fun a => (a + off) ↦₃₂ w) :=
  relocAt_congr_ssmove (fun a => pointsTo32_eq_pointsToBytes (a + off) w)
    (relocAt_pointsToBytes_ssmove k off (unpack32 w) hoff (unpack32_length w))

private theorem relocAt_pointsTo64_ssmove (k : Nat) (off : BitVec 64) (w : BitVec 64)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_ssmove k 8 (fun a => (a + off) ↦₆₄ w) :=
  relocAt_congr_ssmove (fun a => pointsTo64_eq_pointsToBytes (a + off) w)
    (relocAt_pointsToBytes_ssmove k off (unpack64 w) hoff (unpack64_length w))

private theorem relocAt_memRegion_ssmove (k : Nat) (off : BitVec 64) (n : Nat)
    (hoff : off = BitVec.ofNat 64 k) (hn : n ≤ 2 ^ 64) :
    RelocAt_ssmove k n (fun a => memRegion (a + off) n) := by
  subst hoff
  intro a
  dsimp only
  rw [memRegion_eq_exists_bytes (a + BitVec.ofNat 64 k) n hn]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  refine Entails.sepExists_right bs (Entails.sepExists_right emp ?_)
  rw [sepConj_emp]
  refine Entails.pure_right ⟨hlen, fun b => ?_⟩ (Entails.refl _)
  rw [sepConj_emp, ← hlen]
  exact pointsToBytes_entails_memRegion (b + BitVec.ofNat 64 k) bs

private theorem relocAt_const_right_ssmove {k n : Nat} {P : BitVec 64 → SepProp} (H0 : SepProp)
    (hP : RelocAt_ssmove k n P) :
    RelocAt_ssmove k n (fun a => P a ∗ H0) := by
  intro a
  dsimp only
  refine Entails.trans (sepConj_mono_left (hP a)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro bs
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro H
  rw [sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hlen, hrec⟩
  refine Entails.sepExists_right bs (Entails.sepExists_right (H ∗ H0) ?_)
  refine Entails.pure_right ⟨hlen, fun b => ?_⟩ (Entails.refl _)
  rw [← sepConj_assoc]
  exact sepConj_mono_left (hrec b)

private theorem relocAt_exists_ssmove {α : Type} {k n : Nat} {P : α → BitVec 64 → SepProp}
    (hP : ∀ x, RelocAt_ssmove k n (P x)) :
    RelocAt_ssmove k n (fun a => ∃∗ x : α, P x a) := by
  intro a
  dsimp only
  apply Entails.sepExists_elim; intro x
  refine Entails.trans (hP x a) ?_
  apply Entails.sepExists_elim; intro bs
  refine Entails.sepExists_right bs ?_
  apply Entails.sepExists_elim; intro H
  refine Entails.sepExists_right H ?_
  apply Entails.pure_left; rintro ⟨hlen, hrec⟩
  refine Entails.pure_right ⟨hlen, fun b => ?_⟩ (Entails.refl _)
  exact Entails.trans (hrec b) (Entails.sepExists_right x (Entails.refl _))

private theorem bitVec_add_ofNat_add_ssmove (x : BitVec 64) (k n1 k2 : Nat) (hk : k + n1 = k2) :
    x + BitVec.ofNat 64 k + BitVec.ofNat 64 n1 = x + BitVec.ofNat 64 k2 := by
  subst hk
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem relocAt_sep_ssmove {k n1 k2 n2 : Nat} {P1 P2 : BitVec 64 → SepProp}
    (h1 : RelocAt_ssmove k n1 P1) (h2 : RelocAt_ssmove k2 n2 P2)
    (hk2 : k + n1 = k2) :
    RelocAt_ssmove k (n1 + n2) (fun a => P1 a ∗ P2 a) := by
  intro a
  dsimp only
  refine Entails.trans (sepConj_mono (h1 a) (h2 a)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro bs1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro H1
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs2
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro H2
  have hpull1 :
      ((⌜bs1.length = n1 ∧ ∀ b : BitVec 64, (((b + BitVec.ofNat 64 k) ↦ₛ bs1) ∗ H1) ⊢ P1 b⌝ ∗
          ((a + BitVec.ofNat 64 k) ↦ₛ bs1) ∗ H1) ∗
        (⌜bs2.length = n2 ∧ ∀ b : BitVec 64, (((b + BitVec.ofNat 64 k2) ↦ₛ bs2) ∗ H2) ⊢ P2 b⌝ ∗
          ((a + BitVec.ofNat 64 k2) ↦ₛ bs2) ∗ H2)) =
      (⌜bs1.length = n1 ∧ ∀ b : BitVec 64, (((b + BitVec.ofNat 64 k) ↦ₛ bs1) ∗ H1) ⊢ P1 b⌝ ∗
        ⌜bs2.length = n2 ∧ ∀ b : BitVec 64, (((b + BitVec.ofNat 64 k2) ↦ₛ bs2) ∗ H2) ⊢ P2 b⌝ ∗
        (((a + BitVec.ofNat 64 k) ↦ₛ bs1) ∗ ((a + BitVec.ofNat 64 k2) ↦ₛ bs2)) ∗
        (H1 ∗ H2)) := by ac_rfl
  rw [hpull1]
  apply Entails.pure_left; rintro ⟨hlen1, hrec1⟩
  apply Entails.pure_left; rintro ⟨hlen2, hrec2⟩
  refine Entails.sepExists_right (bs1 ++ bs2) (Entails.sepExists_right (H1 ∗ H2) ?_)
  have hlen : (bs1 ++ bs2).length = n1 + n2 := by rw [List.length_append, hlen1, hlen2]
  rw [pointsToBytes_append, hlen1, bitVec_add_ofNat_add_ssmove a k n1 k2 hk2]
  refine Entails.pure_right ⟨hlen, fun b => ?_⟩ (Entails.refl _)
  rw [pointsToBytes_append, hlen1, bitVec_add_ofNat_add_ssmove b k n1 k2 hk2]
  have hpull2 :
      ((((b + BitVec.ofNat 64 k) ↦ₛ bs1) ∗ ((b + BitVec.ofNat 64 k2) ↦ₛ bs2)) ∗ (H1 ∗ H2)) =
      ((((b + BitVec.ofNat 64 k) ↦ₛ bs1) ∗ H1) ∗ (((b + BitVec.ofNat 64 k2) ↦ₛ bs2) ∗ H2)) := by
    ac_rfl
  rw [hpull2]
  exact sepConj_mono (hrec1 b) (hrec2 b)

private theorem relocAt_zero_ssmove {n : Nat} {P : BitVec 64 → SepProp}
    (hP : RelocAt_ssmove 0 n (fun a => P (a + 0#64))) :
    RelocAt_ssmove 0 n P :=
  relocAt_congr_ssmove (fun a => congrArg P (BitVec.add_zero a).symm) hP

private theorem relocAt_shift_ssmove {k n : Nat} {P : BitVec 64 → SepProp} (off : BitVec 64)
    (hoff : off = BitVec.ofNat 64 k) (hP : RelocAt_ssmove 0 n P) :
    RelocAt_ssmove k n (fun a => P (a + off)) := by
  subst hoff
  intro a
  dsimp only
  refine Entails.trans (hP (a + BitVec.ofNat 64 k)) ?_
  apply Entails.sepExists_elim; intro bs
  refine Entails.sepExists_right bs ?_
  apply Entails.sepExists_elim; intro H
  refine Entails.sepExists_right H ?_
  apply Entails.pure_left; rintro ⟨hlen, hrec⟩
  have ha0 : a + BitVec.ofNat 64 k + BitVec.ofNat 64 0 = a + BitVec.ofNat 64 k :=
    BitVec.add_zero _
  rw [ha0]
  refine Entails.pure_right ⟨hlen, fun b => ?_⟩ (Entails.refl _)
  simpa only [BitVec.add_zero] using hrec (b + BitVec.ofNat 64 k)

private theorem relocAt_vecHeader_zero_ssmove (cap ptr len : BitVec 64) :
    RelocAt_ssmove 0 24 (fun a => vecHeader a cap ptr len) :=
  relocAt_sep_ssmove
    (relocAt_zero_ssmove (relocAt_pointsTo64_ssmove 0 0#64 cap rfl))
    (relocAt_sep_ssmove
      (relocAt_pointsTo64_ssmove 8 8#64 ptr rfl)
      (relocAt_pointsTo64_ssmove 16 16#64 len rfl) rfl) rfl

private theorem relocAt_vecHeader_ssmove (k : Nat) (off cap ptr len : BitVec 64)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_ssmove k 24 (fun a => vecHeader (a + off) cap ptr len) :=
  relocAt_shift_ssmove off hoff (relocAt_vecHeader_zero_ssmove cap ptr len)

private theorem relocAt_vecAt_ssmove {α : Type} (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (stride align : Nat) (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_ssmove k 24 (fun a => vecAt A stride align elem (a + off) cap ptr xs) :=
  relocAt_const_right_ssmove (vecBuf A stride align elem cap ptr xs)
    (relocAt_vecHeader_ssmove k off cap ptr (BitVec.ofNat 64 xs.length) hoff)

private theorem relocAt_vecOf_ssmove {α : Type} (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (stride align : Nat) (elem : α → BitVec 64 → SepProp) (xs : List α)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_ssmove k 24 (fun a => vecOf A stride align elem (a + off) xs) :=
  relocAt_exists_ssmove fun cap =>
    relocAt_exists_ssmove fun ptr =>
      relocAt_vecAt_ssmove k off A stride align elem cap ptr xs hoff

private def vecU8Heap_ssmove (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

private theorem relocAt_vecU8At_ssmove (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (cap ptr : BitVec 64) (bs : List (BitVec 8)) (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_ssmove k 24 (fun a => vecU8At A (a + off) cap ptr bs) :=
  relocAt_const_right_ssmove (vecU8Heap_ssmove A cap ptr bs)
    (relocAt_vecHeader_ssmove k off cap ptr (BitVec.ofNat 64 bs.length) hoff)

private theorem relocAt_vecU8_ssmove (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (bs : List (BitVec 8)) (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_ssmove k 24 (fun a => vecU8 A (a + off) bs) :=
  relocAt_exists_ssmove fun cap =>
    relocAt_exists_ssmove fun ptr =>
      relocAt_vecU8At_ssmove k off A cap ptr bs hoff

private theorem relocAt_vecU8_zero_ssmove (A : RustAlloc) (bs : List (BitVec 8)) :
    RelocAt_ssmove 0 24 (fun a => vecU8 A a bs) :=
  relocAt_zero_ssmove (relocAt_vecU8_ssmove 0 0#64 A bs rfl)

private theorem relocAt_prostChainGAt_zero_ssmove (A : RustAlloc) (c : ChainG) :
    RelocAt_ssmove 0 104 (fun a => prostChainGAt A a c) := by
  have hck : RelocAt_ssmove 0x48 32 (fun a =>
      match c.ck with
      | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
      | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
          memRegion (a + 0x64#64) 4) := by
    cases c.ck with
    | none =>
      exact relocAt_sep_ssmove
        (relocAt_pointsTo64_ssmove 0x48 0x48#64 noneCap rfl)
        (relocAt_memRegion_ssmove 0x50 0x50#64 24 rfl (by decide)) rfl
    | some ik =>
      rcases ik with ⟨i, k⟩
      exact relocAt_sep_ssmove (relocAt_vecU8_ssmove 0x48 0x48#64 A k rfl)
        (relocAt_sep_ssmove (relocAt_pointsTo32_ssmove 0x60 0x60#64 i rfl)
          (relocAt_memRegion_ssmove 0x64 0x64#64 4 rfl (by decide)) rfl) rfl
  exact relocAt_sep_ssmove (relocAt_vecU8_zero_ssmove A c.srk)
    (relocAt_sep_ssmove (relocAt_vecU8_ssmove 0x18 0x18#64 A c.priv rfl)
      (relocAt_sep_ssmove
        (relocAt_vecOf_ssmove 0x30 0x30#64 A 104 8 (fun mk b => prostMsgKeyAt A mk b) c.keys rfl)
        hck rfl) rfl) rfl

private def prostSSGAfterLik_ssmove (A : RustAlloc) (v : SSG) (ss : BitVec 64) : SepProp :=
  vecU8 A (ss + 0x18#64) v.rik ∗ vecU8 A (ss + 0x30#64) v.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.recv ∗
    vecU8 A (ss + 0x60#64) [] ∗ vecU8 A (ss + 0x78#64) [] ∗
    (match v.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.prevCounter) ∗
    ((ss + 0x150#64) ↦₆₄ 0#64)

private theorem relocAt_prostSSGAfterLik_ssmove (A : RustAlloc) (v : SSG) :
    RelocAt_ssmove 0x18 320 (prostSSGAfterLik_ssmove A v) := by
  have hsender : RelocAt_ssmove 0x90 104 (fun ss =>
      match v.sender with
      | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
      | some c => prostChainGAt A (ss + 0x90#64) c) := by
    cases v.sender with
    | none =>
      exact relocAt_sep_ssmove
        (relocAt_pointsTo64_ssmove 0x90 0x90#64 noneCap rfl)
        (relocAt_memRegion_ssmove 0x98 0x98#64 96 rfl (by decide)) rfl
    | some c =>
      exact relocAt_shift_ssmove 0x90#64 rfl (relocAt_prostChainGAt_zero_ssmove A c)
  have hpending : RelocAt_ssmove 0xf8 48 (fun ss =>
      match v.pending with
      | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
      | some k => vecU8 A (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
          memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
          ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) := by
    cases v.pending with
    | none =>
      exact relocAt_sep_ssmove
        (relocAt_pointsTo64_ssmove 0xf8 0xf8#64 noneCap rfl)
        (relocAt_memRegion_ssmove 0x100 0x100#64 40 rfl (by decide)) rfl
    | some k =>
      exact relocAt_sep_ssmove (relocAt_vecU8_ssmove 0xf8 0xf8#64 A k rfl)
        (relocAt_sep_ssmove (relocAt_pointsTo32_ssmove 0x110 0x110#64 0#32 rfl)
          (relocAt_sep_ssmove (relocAt_memRegion_ssmove 0x114 0x114#64 4 rfl (by decide))
            (relocAt_sep_ssmove (relocAt_pointsTo64_ssmove 0x118 0x118#64 0#64 rfl)
              (relocAt_sep_ssmove (relocAt_pointsTo32_ssmove 0x120 0x120#64 0#32 rfl)
                (relocAt_memRegion_ssmove 0x124 0x124#64 4 rfl (by decide)) rfl)
              rfl) rfl) rfl) rfl
  exact relocAt_sep_ssmove (relocAt_vecU8_ssmove 0x18 0x18#64 A v.rik rfl)
    (relocAt_sep_ssmove (relocAt_vecU8_ssmove 0x30 0x30#64 A v.root rfl)
      (relocAt_sep_ssmove
        (relocAt_vecOf_ssmove 0x48 0x48#64 A 104 8 (fun c a => prostChainGAt A a c) v.recv rfl)
        (relocAt_sep_ssmove (relocAt_vecU8_ssmove 0x60 0x60#64 A [] rfl)
          (relocAt_sep_ssmove (relocAt_vecU8_ssmove 0x78 0x78#64 A [] rfl)
            (relocAt_sep_ssmove hsender
              (relocAt_sep_ssmove hpending
                (relocAt_sep_ssmove (relocAt_pointsTo64_ssmove 0x128 0x128#64 noneCap rfl)
                  (relocAt_sep_ssmove (relocAt_memRegion_ssmove 0x130 0x130#64 24 rfl (by decide))
                    (relocAt_sep_ssmove (relocAt_pointsTo32_ssmove 0x148 0x148#64 v.version rfl)
                      (relocAt_sep_ssmove
                        (relocAt_pointsTo32_ssmove 0x14c 0x14c#64 v.prevCounter rfl)
                        (relocAt_pointsTo64_ssmove 0x150 0x150#64 0#64 rfl) rfl)
                      rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl

private def likTail_ssmove (A : RustAlloc) (w0 ptr : BitVec 64) (lik : List (BitVec 8))
    (ss : BitVec 64) : SepProp :=
  (((ss + 8#64) ↦₆₄ ptr) ∗ ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 lik.length)) ∗
    vecU8Heap_ssmove A w0 ptr lik

private theorem relocAt_likTail_ssmove (A : RustAlloc) (w0 ptr : BitVec 64)
    (lik : List (BitVec 8)) :
    RelocAt_ssmove 8 16 (likTail_ssmove A w0 ptr lik) :=
  relocAt_const_right_ssmove (vecU8Heap_ssmove A w0 ptr lik)
    (relocAt_sep_ssmove
      (relocAt_pointsTo64_ssmove 8 8#64 ptr rfl)
      (relocAt_pointsTo64_ssmove 16 16#64 (BitVec.ofNat 64 lik.length) rfl) rfl)

private def prostSSGTail_ssmove (A : RustAlloc) (w0 ptr : BitVec 64) (v : SSG)
    (ss : BitVec 64) : SepProp :=
  likTail_ssmove A w0 ptr v.lik ss ∗ prostSSGAfterLik_ssmove A v ss

private theorem relocAt_prostSSGTail_ssmove (A : RustAlloc) (w0 ptr : BitVec 64) (v : SSG) :
    RelocAt_ssmove 8 336 (prostSSGTail_ssmove A w0 ptr v) :=
  relocAt_sep_ssmove (relocAt_likTail_ssmove A w0 ptr v.lik)
    (relocAt_prostSSGAfterLik_ssmove A v) rfl

private theorem vecU8At_eq_word0_sep_likTail_ssmove (A : RustAlloc) (ss w0 ptr : BitVec 64)
    (lik : List (BitVec 8)) :
    vecU8At A ss w0 ptr lik = (ss ↦₆₄ w0) ∗ likTail_ssmove A w0 ptr lik ss := by
  unfold vecU8At vecHeader likTail_ssmove vecU8Heap_ssmove
  ac_rfl

private theorem vecU8At_entails_vecU8_ssmove (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢ vecU8 A v bs := by
  unfold vecU8
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

private theorem vecU8Heap_w0_ne_noneCap_ssmove (A : RustAlloc) (w0 ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8Heap_ssmove A w0 ptr bs ⊢ ⌜w0 ≠ noneCap⌝ ∗ vecU8Heap_ssmove A w0 ptr bs := by
  unfold vecU8Heap_ssmove
  apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
  have hne : w0 ≠ noneCap := by
    intro heq; subst heq; revert hlt; decide
  exact Entails.pure_right hne (Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _))

private theorem likTail_w0_ne_noneCap_ssmove (A : RustAlloc) (w0 ptr : BitVec 64)
    (lik : List (BitVec 8)) (ss : BitVec 64) :
    likTail_ssmove A w0 ptr lik ss ⊢ ⌜w0 ≠ noneCap⌝ ∗ likTail_ssmove A w0 ptr lik ss := by
  unfold likTail_ssmove
  refine Entails.trans (sepConj_mono_right (vecU8Heap_w0_ne_noneCap_ssmove A w0 ptr lik)) ?_
  rw [sepConj_pure_left_comm]
  exact Entails.refl _

private theorem word0_sep_prostSSGTail_entails_prostSSGAt_ssmove (A : RustAlloc)
    (b w0 ptr : BitVec 64) (v : SSG) :
    ((b ↦₆₄ w0) ∗ prostSSGTail_ssmove A w0 ptr v b) ⊢ prostSSGAt A b v := by
  change ((b ↦₆₄ w0) ∗ (likTail_ssmove A w0 ptr v.lik b ∗ prostSSGAfterLik_ssmove A v b)) ⊢
    (vecU8 A b v.lik ∗ prostSSGAfterLik_ssmove A v b)
  rw [← sepConj_assoc, ← vecU8At_eq_word0_sep_likTail_ssmove]
  exact sepConj_mono_left (vecU8At_entails_vecU8_ssmove A b w0 ptr v.lik)

private theorem prostSSGAt_move_loopExit (A : RustAlloc) (a : BitVec 64) (v : SSG) :
    prostSSGAt A a v ⊢
      ∃∗ w0 : BitVec 64, ∃∗ rest : List (BitVec 8), ∃∗ H : SepProp,
        ⌜w0 ≠ noneCap ∧ rest.length = 336 ∧
          ∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ rest) ∗ H) ⊢ prostSSGAt A b v⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ rest) ∗ H := by
  change (vecU8 A a v.lik ∗ prostSSGAfterLik_ssmove A v a) ⊢ _
  unfold vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w0
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  rw [vecU8At_eq_word0_sep_likTail_ssmove, sepConj_assoc]
  change ((a ↦₆₄ w0) ∗ prostSSGTail_ssmove A w0 ptr v a) ⊢ _
  have hne_step :
      prostSSGTail_ssmove A w0 ptr v a ⊢
        ⌜w0 ≠ noneCap⌝ ∗ prostSSGTail_ssmove A w0 ptr v a := by
    unfold prostSSGTail_ssmove
    refine Entails.trans (sepConj_mono_left (likTail_w0_ne_noneCap_ssmove A w0 ptr v.lik a)) ?_
    rw [sepConj_assoc]
    exact Entails.refl _
  refine Entails.trans (sepConj_mono_right hne_step) ?_
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hw0
  refine Entails.trans (sepConj_mono_right (relocAt_prostSSGTail_ssmove A w0 ptr v a)) ?_
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro rest
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro H
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hrest_len, hrec⟩
  refine Entails.sepExists_right w0
    (Entails.sepExists_right rest (Entails.sepExists_right H ?_))
  have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
  rw [h8]
  refine Entails.pure_right ⟨hw0, hrest_len, fun b => ?_⟩ (Entails.refl _)
  exact Entails.trans (sepConj_mono_right (hrec b))
    (word0_sep_prostSSGTail_entails_prostSSGAt_ssmove A b w0 ptr v)

/-! ## Loop exit stepping on `SP2Ext` -/

private theorem fnOff_deser_loopExit :
    libsignalSessionCode.fnOff recDeserializeName = num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") := by
  exact (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize")

local elab "dexit_code_fetches_from " codeId:ident b:term:max H:term:max hfn:term:max
    off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let fetchEntry := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := Lean.mkIdent (Lean.Name.str `CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopExitG s!"loopExit_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Lean.Syntax.mkNumLit (toString k)
    if k == 0 then
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

local macro "dexit_fetches " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| dexit_code_fetches_from CryptoVerification.libsignalSessionCode $b $H
    fnOff_deser_loopExit (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) $k0 $len)

private theorem int64_raw_toBitVec_loopExit (n : Nat) (h : n < 18446744073709551616) :
    ({ toUInt64 := { toBitVec := { toFin := ⟨n, h⟩ } } } : Int64).toBitVec = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  change n = n % 18446744073709551616
  exact (Nat.mod_eq_of_lt h).symm

attribute [local arm64_norm] int64_raw_toBitVec_loopExit

private theorem w0_add_one_ne_zero_loopExit {w0 : BitVec 64} (h : w0 ≠ noneCap) :
    w0 + 1#64 ≠ 0#64 := by
  unfold noneCap at h
  bv_omega

private theorem w0_add_one_beq_zero_loopExit {w0 : BitVec 64} (h : w0 ≠ noneCap) :
    (w0 + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact w0_add_one_ne_zero_loopExit h

def deserSavedAtL_loopExit (L : BitVec 64) (s0 : State) : SepProp :=
  ((L + 0x710#64) ↦₆₄ s0.readReg64 .x29) ∗ ((L + 0x718#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((L + 0x720#64) ↦₆₄ s0.readReg64 .x28) ∗ ((L + 0x728#64) ↦₆₄ s0.readReg64 .x27) ∗
    ((L + 0x730#64) ↦₆₄ s0.readReg64 .x26) ∗ ((L + 0x738#64) ↦₆₄ s0.readReg64 .x25) ∗
    ((L + 0x740#64) ↦₆₄ s0.readReg64 .x24) ∗ ((L + 0x748#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((L + 0x750#64) ↦₆₄ s0.readReg64 .x22) ∗ ((L + 0x758#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((L + 0x760#64) ↦₆₄ s0.readReg64 .x20) ∗ ((L + 0x768#64) ↦₆₄ s0.readReg64 .x19)

private theorem deserSaved_eq_atL_loopExit (s0 : State) :
    deserSaved s0 = deserSavedAtL_loopExit (deserSpL s0.sp) s0 := by
  unfold deserSaved deserSavedAtL_loopExit deserSpL
  have h0 : s0.sp - 0x60#64 = s0.sp - 0x770#64 + 0x710#64 := by bv_omega
  rw [h0]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem sliceCursorAfter_nil_loopExit (L p : BitVec 64) (bs : List (BitVec 8)) :
    Prost.sliceCursorAfter (L + 0x3f8#64) p bs [] =
      ((L + 0x3f8#64) ↦₆₄ (p + BitVec.ofNat 64 bs.length)) ∗
        ((L + 0x400#64) ↦₆₄ 0#64) ∗ (p ↦ₛ bs) := by
  unfold Prost.sliceCursorAfter
  have h : L + 0x3f8#64 + 8#64 = L + 0x400#64 := by bv_omega
  rw [h, List.length_nil, Nat.sub_zero]

private theorem memRegion_3f8_split_loopExit (L : BitVec 64) :
    memRegion L 0x3f8 =
      memRegion L 8 ∗
        (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗
          memRegion (L + 0x2a8#64) 336) := by
  rw [memRegion_split' (b := L) (b' := L + 8#64) (N := 0x3f8) (n := 8) (k := 1008)
        (by decide) rfl (by decide),
      memRegion_split' (b := L + 8#64) (b' := L + 0x158#64) (N := 1008) (n := 336) (k := 672)
        (by decide) (by bv_omega) (by decide),
      memRegion_split' (b := L + 0x158#64) (b' := L + 0x2a8#64) (N := 672) (n := 336) (k := 336)
        (by decide) (by bv_omega) (by decide)]

private theorem memRegion_out_split_loopExit (out : BitVec 64) :
    memRegion out 368 =
      ∃∗ u3 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗
          ((out + 0x10#64) ↦₆₄ u2) ∗ ((out + 0x18#64) ↦₆₄ u3) ∗
          memRegion (out + 0x20#64) 336 := by
  rw [memRegion_split' (b := out) (b' := out + 8#64) (N := 368) (n := 8) (k := 360)
        (by decide) rfl (by decide),
      memRegion_split' (b := out + 8#64) (b' := out + 0x10#64) (N := 360) (n := 8) (k := 352)
        (by decide) (by bv_omega) (by decide),
      memRegion_split' (b := out + 0x10#64) (b' := out + 0x18#64) (N := 352) (n := 8) (k := 344)
        (by decide) (by bv_omega) (by decide),
      memRegion_split' (b := out + 0x18#64) (b' := out + 0x20#64) (N := 344) (n := 8) (k := 336)
        (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_eight out, ProofLib.memRegion_eight (out + 8#64),
      ProofLib.memRegion_eight (out + 0x10#64), ProofLib.memRegion_eight (out + 0x18#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

private theorem satisfies_memRegion_out_split_loopExit {m : Memory} {out : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion out 368 ∗ R) :
    ∃ u0 u1 u2 u3 : BitVec 64,
      m ⊨ ((out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗
        ((out + 0x10#64) ↦₆₄ u2) ∗ ((out + 0x18#64) ↦₆₄ u3) ∗
        memRegion (out + 0x20#64) 336) ∗ R := by
  rw [memRegion_out_split_loopExit out] at h
  simp only [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨u3, u2, u1, u0, h⟩
  exact ⟨u0, u1, u2, u3, by simpa only [sepConj_assoc] using h⟩

private theorem satisfies_prostSSGAt_move_loopExit {A : RustAlloc} {m : Memory} {L : BitVec 64} {v : SSG} {R : SepProp}
    (h : m ⊨ prostSSGAt A (L + 0x420#64) v ∗ R) :
    ∃ w0 : BitVec 64, ∃ rest : List (BitVec 8), ∃ H : SepProp,
      w0 ≠ noneCap ∧ rest.length = 336 ∧
      (∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ rest) ∗ H) ⊢ prostSSGAt A b v) ∧
      (m ⊨ (((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ H) ∗ R) := by
  have h428 : L + 0x420#64 + 8#64 = L + 0x428#64 := by bv_omega
  have hmove_ent := prostSSGAt_move_loopExit A (L + 0x420#64) v
  rw [h428] at hmove_ent
  have h1 := Satisfies.mono (sepConj_mono_left hmove_ent) h
  simp only [sepExists_sepConj_left, satisfies_sepExists] at h1
  rcases h1 with ⟨w0, rest, H, h1⟩
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hw0, hrest, hrebuild⟩, h1⟩
  exact ⟨w0, rest, H, hw0, hrest, hrebuild, by simpa only [sepConj_assoc] using h1⟩

private theorem deserSavedAtL_entails_memRegion_loopExit (L : BitVec 64) (s0 : State) :
    deserSavedAtL_loopExit L s0 ⊢ memRegion (L + 0x710#64) 0x60 := by
  unfold deserSavedAtL_loopExit
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))))))))))) ?_
  have join (n : Nat) (h : n + 8 ≤ 2 ^ 64) :
      memRegion (L + 0x710#64) n ∗ memRegion (L + BitVec.ofNat 64 (0x710 + n)) 8 =
      memRegion (L + 0x710#64) (n + 8) :=
    (memRegion_split' (b := L + 0x710#64) (b' := L + BitVec.ofNat 64 (0x710 + n))
      (n := n) (k := 8) rfl (by bv_omega) h).symm
  simp only [← sepConj_assoc]
  rw [join 8 (by decide), join 16 (by decide), join 24 (by decide),
      join 32 (by decide), join 40 (by decide), join 48 (by decide),
      join 56 (by decide), join 64 (by decide), join 72 (by decide),
      join 80 (by decide), join 88 (by decide)]
  exact Entails.refl _

private theorem dexit_locals_entails_memRegion_loopExit (L c0 w0 : BitVec 64) (s0 : State)
    (rest : List (BitVec 8)) (hrest : rest.length = 336) :
    memRegion L 8 ∗
      ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
      ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗
      ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
      ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
      memRegion (L + 0x578#64) 0x170 ∗
      ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
      memRegion (L + 0x6f0#64) 0x20 ∗
      deserSavedAtL_loopExit L s0 ⊢
      memRegion L 0x770 := by
  have hb (a : BitVec 64) : (a ↦ₛ rest) ⊢ memRegion a 336 := by
    rw [← hrest]
    exact ProofLib.pointsToBytes_entails_memRegion a rest
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (hb (L + 8#64)) (sepConj_mono (hb (L + 0x158#64))
      (sepConj_mono (hb (L + 0x2a8#64)) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (hb (L + 0x428#64))
      (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_right (deserSavedAtL_entails_memRegion_loopExit L s0))))))))))))))) ?_
  have join (n k : Nat) (h : n + k ≤ 2 ^ 64) :
      memRegion L n ∗ memRegion (L + BitVec.ofNat 64 n) k = memRegion L (n + k) :=
    (memRegion_split' (b := L) (b' := L + BitVec.ofNat 64 n) (n := n) (k := k) rfl rfl h).symm
  simp only [← sepConj_assoc]
  rw [join 8 336 (by decide), join 344 336 (by decide), join 680 336 (by decide),
      join 1016 8 (by decide), join 1024 8 (by decide), join 1032 8 (by decide),
      join 1040 8 (by decide), join 1048 8 (by decide), join 1056 8 (by decide),
      join 1064 336 (by decide), join 1400 0x170 (by decide), join 1768 8 (by decide),
      join 1776 0x20 (by decide), join 1808 0x60 (by decide)]
  exact Entails.refl _

private theorem dexit_frame_entails_stackAt_loopExit (s0 : State) (c0 w0 : BitVec 64)
    (rest : List (BitVec 8)) (hrest : rest.length = 336) :
    let L := deserSpL s0.sp
    stackAt L deserCalleeStack ∗
      (memRegion L 8 ∗
        ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
        ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗
        ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
        ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
        memRegion (L + 0x578#64) 0x170 ∗
        ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
        memRegion (L + 0x6f0#64) 0x20 ∗
        deserSavedAtL_loopExit L s0) ⊢
      stackAt s0.sp recDeserializeStack := by
  intro L
  refine Entails.trans
    (sepConj_mono_right (dexit_locals_entails_memRegion_loopExit L c0 w0 s0 rest hrest)) ?_
  unfold stackAt
  have h1 : s0.sp - BitVec.ofNat 64 recDeserializeStack = L - BitVec.ofNat 64 deserCalleeStack := by
    dsimp [L, deserSpL, recDeserializeStack, deserCalleeStack]
    bv_omega
  rw [h1,
    memRegion_split' (b := L - BitVec.ofNat 64 deserCalleeStack) (b' := L)
      (N := recDeserializeStack) (n := deserCalleeStack) (k := 0x770) (by decide)
      (by dsimp [deserCalleeStack, recDeserializeStack]; bv_omega)
      (by decide)]
  exact Entails.refl _

@[local simp, local wp_norm, local arm64_norm]
private theorem frozenLoaded_writeReg64_ext (img : Obj.Image) (s : State) (r : Reg) (v : BitVec 64) :
    img.FrozenLoaded (s.writeReg64 r v) = img.FrozenLoaded s :=
  propext ⟨frozenLoaded_of_mem_eq rfl, frozenLoaded_of_mem_eq rfl⟩

@[local simp, local wp_norm, local arm64_norm]
private theorem frozenLoaded_writeReg32_ext (img : Obj.Image) (s : State) (r : Reg) (v : BitVec 32) :
    img.FrozenLoaded (s.writeReg32 r v) = img.FrozenLoaded s :=
  propext ⟨frozenLoaded_of_mem_eq rfl, frozenLoaded_of_mem_eq rfl⟩

@[local simp, local wp_norm, local arm64_norm]
private theorem frozenLoaded_setPC_ext (img : Obj.Image) (s : State) (pc : BitVec 64) :
    img.FrozenLoaded (s.setPC pc) = img.FrozenLoaded s :=
  propext ⟨frozenLoaded_of_mem_eq rfl, frozenLoaded_of_mem_eq rfl⟩

@[local simp, local wp_norm, local arm64_norm]
private theorem frozenLoaded_setPState_ext (img : Obj.Image) (s : State) (ps : PState) :
    img.FrozenLoaded (s.setPState ps) = img.FrozenLoaded s :=
  propext ⟨frozenLoaded_of_mem_eq rfl, frozenLoaded_of_mem_eq rfl⟩

@[local simp, local wp_norm, local arm64_norm]
private theorem frozenLoaded_writeVReg128_ext (img : Obj.Image) (s : State) (idx : BitVec 5) (v : BitVec 128) :
    img.FrozenLoaded (s.writeVReg128 idx v) = img.FrozenLoaded s :=
  propext ⟨frozenLoaded_of_mem_eq rfl, frozenLoaded_of_mem_eq rfl⟩

@[local simp, local wp_norm, local arm64_norm]
private theorem symtab_setPState_ext (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := rfl

private theorem fnOff_deser_memcpy_loopExit :
    libsignalSessionCode.fnOff recDeserializeName +
      num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") =
      libsignalSessionCode.fnOff memcpyName := by
  rw [fnOff_deser_loopExit]
  decide

theorem memcpy_ok_extW {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsA0 img ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))
      ((sessionMemcpySpec deserCalleeStack).inImage img) :=
  subroutine_ok_sessionMemcpySpec_mono (s2 := deserCalleeStack) (by decide) (by decide)
    (hC.memcpy_ok_at fnOff_deser_memcpy_loopExit)

private theorem memcpy_ok_inv_ext {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hmc_ok : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))
      ((sessionMemcpySpec deserCalleeStack).inImage img)) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))
      { pre := ((sessionMemcpySpec deserCalleeStack).inImage img).pre
        post := fun a s0 sf => ⌜img.FrozenLoaded sf ∧ sf.symtab = img.symtab⌝ ∗ (sessionMemcpySpec deserCalleeStack).post a s0 sf } := by
  apply subroutine_ok_of_sepWP_init
  intro x R s0 hpc hrun hm hsp
  have hm_in := hm
  dsimp only [Spec.inImage] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hfrozen, hsym⟩, -⟩
  refine ⟨((sessionMemcpySpec deserCalleeStack).inImage img).pre x s0, hm_in, ?_⟩
  refine SepWP.call_subroutine_frame_frozen (F := emp) hmc_ok hfrozen hsym hpc hrun hsp rfl
    (fun _ hm' => by simpa [emp_sepConj] using hm')
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_
    (fun _ _ _ h => (not_satisfies_false_sepConj h).elim)
  intro sf hpcf hrunf hspf hcsf hf_frozen hf_sym
  refine SepWP.done hpcf hrunf ⟨fun hmf => ?_, hspf, hcsf⟩
  dsimp only [Spec.inImage] at hmf ⊢
  rw [sepConj_emp] at hmf
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hf_frozen, hf_sym⟩, hmf⟩

set_option maxHeartbeats 800000 in
private theorem dexit_sepWP_loopExit_ext {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hmc_ok : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))
      ((sessionMemcpySpec deserCalleeStack).inImage img))
    {s0 s : State} {L out w0 u0 u1 u2 u3 : BitVec 64} {rest : List (BitVec 8)}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 0x254#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = L)
    (hal : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = L + 0x710#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hw0 : w0 ≠ noneCap)
    (hrest : rest.length = 336)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (SP2Ext img.base ext) (s0.readReg64 .lr) s
      (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336 ∗
        ((L + 0x400#64) ↦₆₄ 0#64) ∗
        ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
        ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
        ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
        (out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗
        ((out + 0x10#64) ↦₆₄ u2) ∗ ((out + 0x18#64) ↦₆₄ u3) ∗
        memRegion (out + 0x20#64) 336 ∗
        stackAt L deserCalleeStack ∗
        deserSavedAtL_loopExit L s0)
      (fun sf P_f =>
        sf.sp = L + 0x770#64 ∧
        sf.trace = s.trace ∧
        CalleeSavedPreserved s0 sf ∧
        P_f = (((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
          ((L + 0x400#64) ↦₆₄ 0#64) ∗
          ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
          ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗
          ((out + 0x10#64) ↦₆₄ 0#64) ∗ ((out + 0x18#64) ↦₆₄ w0) ∗
          ((out + 0x20#64) ↦ₛ rest) ∗
          stackAt L deserCalleeStack ∗
          deserSavedAtL_loopExit L s0)) := by
  subst hsp
  have hmemcpy := memcpy_ok_inv_ext hmc_ok
  have hw0_ne := w0_add_one_ne_zero_loopExit hw0
  have hw0_beq := w0_add_one_beq_zero_loopExit hw0
  dexit_fetches img.base (Rust.withPanics ext) 492 20
  dexit_fetches img.base (Rust.withPanics ext) 596 16
  dexit_fetches img.base (Rust.withPanics ext) 780 4
  dexit_fetches img.base (Rust.withPanics ext) 852 68
  dexit_fetches img.base (Rust.withPanics ext) 1208 32
  dexit_fetches img.base (Rust.withPanics ext) 1248 44
  dsimp only [SP2Ext, contractProg] at hpc hmemcpy ⊢
  generalize (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr recDeserializeName = entry at *
  examples_hide_fetches
  unfold deserSavedAtL_loopExit
  wp_steps
  wp_call hmemcpy (s.sp + 8#64, s.sp + 0x428#64, rest)
  wp_steps
  wp_call hmemcpy (s.sp + 0x2a8#64, s.sp + 8#64, rest)
  wp_steps
  wp_call hmemcpy (s.sp + 0x158#64, s.sp + 0x2a8#64, rest)
  apply ProofLib.SepWP.of_sepWP_inv (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) (by assumption) (by assumption)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF_c4 hsym_c4
  wp_call hmemcpy (out + 0x20#64, s.sp + 0x158#64, rest)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]; ac_rfl

theorem deserLoopExitG_ok_of_memcpy
    (img : Obj.Image) (ext : String → Option (State → State))
    (hmc_ok : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))
      ((sessionMemcpySpec deserCalleeStack).inImage img))
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State) (hr : DeserializeScope x.r)
    (hs : DeserLoopGAtW img ext x R s0 (recFields x.r).length s) :
    DeserStepGAtW img ext x R s0 s (DeserRetGAt img x R s0) := by
  let _ := hr
  rcases hs with ⟨hpc, hrun, ⟨htr, hvregs⟩, hsym, hfr, hsp, hal, hx29, hx19, hx20, _hx23, hmem⟩
  let L := deserSpL s0.sp
  let v := ssgAfter x.r (recFields x.r).length
  let bs := encodeRecord x.r
  have hmem : s.mem ⊨ deserLocalsG L x.p bs
      (((recFields x.r).drop (recFields x.r).length).flatMap GenField.enc) v ∗
    memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R := hmem
  rw [List.drop_length, List.flatMap_nil] at hmem
  unfold deserLocalsG at hmem
  rw [sliceCursorAfter_nil_loopExit L x.p bs, memRegion_3f8_split_loopExit L,
      deserSaved_eq_atL_loopExit s0] at hmem
  let c0 := x.p + BitVec.ofNat 64 bs.length
  have hmem1 : s.mem ⊨
      prostSSGAt A0 (L + 0x420#64) v ∗
      (memRegion x.out 368 ∗
       memRegion L 8 ∗
       (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗
         memRegion (L + 0x2a8#64) 336) ∗
       ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (x.p ↦ₛ bs) ∗
       ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
       memRegion (L + 0x578#64) 0x170 ∗
       ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20 ∗
       stackAt L deserCalleeStack ∗ deserSavedAtL_loopExit L s0 ∗ R) := by
    dsimp only [c0]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  obtain ⟨w0, rest, H, hw0, hrest, hrebuild, hmem2⟩ := satisfies_prostSSGAt_move_loopExit hmem1
  have hmem3 : s.mem ⊨
      memRegion x.out 368 ∗
      (((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ H ∗
       memRegion L 8 ∗
       (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗
         memRegion (L + 0x2a8#64) 336) ∗
       ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (x.p ↦ₛ bs) ∗
       ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
       memRegion (L + 0x578#64) 0x170 ∗
       ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20 ∗
       stackAt L deserCalleeStack ∗ deserSavedAtL_loopExit L s0 ∗ R) := by
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem2
  obtain ⟨u0, u1, u2, u3, hmem3'⟩ := satisfies_memRegion_out_split_loopExit hmem3
  let F := (x.p ↦ₛ bs) ∗ H ∗ memRegion L 8 ∗
    ((L + 0x3f8#64) ↦₆₄ c0) ∗ memRegion (L + 0x578#64) 0x170 ∗
    memRegion (L + 0x6f0#64) 0x20 ∗ R
  have hmem4 : s.mem ⊨
      (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336 ∗
        ((L + 0x400#64) ↦₆₄ 0#64) ∗
        ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
        ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
        ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
        (x.out ↦₆₄ u0) ∗ ((x.out + 8#64) ↦₆₄ u1) ∗
        ((x.out + 0x10#64) ↦₆₄ u2) ∗ ((x.out + 0x18#64) ↦₆₄ u3) ∗
        memRegion (x.out + 0x20#64) 336 ∗
        stackAt L deserCalleeStack ∗
        deserSavedAtL_loopExit L s0) ∗ F := by
    dsimp only [F]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem3'
  intro hL
  have hwp := dexit_sepWP_loopExit_ext hmc_ok (s0 := s0) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
    hpc hrun hsp hal hx29 hx19 hx20 hw0 hrest hfr hsym hvregs
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hspf, htracef, hcsf, rfl⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hmem4 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hspf0 : sf.sp = s0.sp := by
    rw [hspf]
    dsimp [L, deserSpL]
    bv_omega
  refine ⟨sf, hsteps, Or.inl ⟨⟨hpcf, hspf0, hrunf⟩, ⟨hspf0, hcsf⟩, ?_⟩⟩
  have hmf1 : sf.mem ⊨
      ((x.p ↦ₛ bs) ∗
       ((x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ 8#64) ∗ ((x.out + 0x10#64) ↦₆₄ 0#64) ∗
         (((x.out + 0x18#64) ↦₆₄ w0) ∗ ((x.out + 0x20#64) ↦ₛ rest) ∗ H)) ∗
       (stackAt L deserCalleeStack ∗
        (memRegion L 8 ∗
          ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
          ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗
          ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
          ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
          memRegion (L + 0x578#64) 0x170 ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          memRegion (L + 0x6f0#64) 0x20 ∗
          deserSavedAtL_loopExit L s0))) ∗ R := by
    dsimp only [F, L] at hmf ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf
  have hout20 : x.out + 0x18#64 + 8#64 = x.out + 0x20#64 := by bv_omega
  have hss_out :
      ((x.out + 0x18#64) ↦₆₄ w0) ∗ ((x.out + 0x20#64) ↦ₛ rest) ∗ H ⊢
        prostSSGAt A0 (x.out + 0x18#64) v := by
    have hr := hrebuild (x.out + 0x18#64)
    rwa [hout20] at hr
  have hstk := dexit_frame_entails_stackAt_loopExit s0 c0 w0 rest hrest
  dsimp only at hstk
  have hmf2 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hss_out))) hstk))) hmf1
  unfold deserOutRawG deserOutRecordG
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htracef.trans htr, ?_⟩
  dsimp only [v, bs] at hmf2
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf2

theorem deserLoopExitG_ok_extW
    (img : Obj.Image)
    (ext : String → Option (State → State))
    (hC : Stage2ContractsA0 img ext)
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State) (hr : DeserializeScope x.r)
    (hs : DeserLoopGAtW img ext x R s0 (recFields x.r).length s) :
    DeserStepGAtW img ext x R s0 s (DeserRetGAt img x R s0) :=
  deserLoopExitG_ok_of_memcpy img ext (memcpy_ok_extW hC) x R s0 s hr hs

theorem memcpy_ok_extWA {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsA img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))
      ((sessionMemcpySpec deserCalleeStack).inImage img) :=
  subroutine_ok_sessionMemcpySpec_mono (s2 := deserCalleeStack) (by decide) (by decide)
    (hC.memcpy_ok_at fnOff_deser_memcpy_loopExit)

theorem deserLoopExitG_ok_of_memcpyA
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hmc_ok : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))
      ((sessionMemcpySpec deserCalleeStack).inImage img))
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State) (hr : DeserializeScope x.r)
    (hs : DeserLoopGAtWA img A ext x R s0 (recFields x.r).length s) :
    DeserStepGAtWA img A ext x R s0 s (DeserRetGAtA img A x R s0) := by
  let _ := hr
  rcases hs with ⟨hpc, hrun, ⟨htr, hvregs⟩, hsym, hfr, hsp, hal, hx29, hx19, hx20, _hx23, hmem⟩
  let L := deserSpL s0.sp
  let v := ssgAfter x.r (recFields x.r).length
  let bs := encodeRecord x.r
  have hmem : s.mem ⊨ deserLocalsGA A L x.p bs
      (((recFields x.r).drop (recFields x.r).length).flatMap GenField.enc) v ∗
    memRegion x.out 368 ∗ A.pool ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R := hmem
  rw [List.drop_length, List.flatMap_nil] at hmem
  unfold deserLocalsGA at hmem
  rw [sliceCursorAfter_nil_loopExit L x.p bs, memRegion_3f8_split_loopExit L,
      deserSaved_eq_atL_loopExit s0] at hmem
  let c0 := x.p + BitVec.ofNat 64 bs.length
  have hmem1 : s.mem ⊨
      prostSSGAt A (L + 0x420#64) v ∗
      (memRegion x.out 368 ∗
       memRegion L 8 ∗
       (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗
         memRegion (L + 0x2a8#64) 336) ∗
       ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (x.p ↦ₛ bs) ∗
       ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
       memRegion (L + 0x578#64) 0x170 ∗
       ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20 ∗
       stackAt L deserCalleeStack ∗ deserSavedAtL_loopExit L s0 ∗ (A.pool ∗ R)) := by
    dsimp only [c0]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  obtain ⟨w0, rest, H, hw0, hrest, hrebuild, hmem2⟩ := satisfies_prostSSGAt_move_loopExit hmem1
  have hmem3 : s.mem ⊨
      memRegion x.out 368 ∗
      (((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ H ∗
       memRegion L 8 ∗
       (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗
         memRegion (L + 0x2a8#64) 336) ∗
       ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (x.p ↦ₛ bs) ∗
       ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
       memRegion (L + 0x578#64) 0x170 ∗
       ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20 ∗
       stackAt L deserCalleeStack ∗ deserSavedAtL_loopExit L s0 ∗ (A.pool ∗ R)) := by
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem2
  obtain ⟨u0, u1, u2, u3, hmem3'⟩ := satisfies_memRegion_out_split_loopExit hmem3
  let F := (x.p ↦ₛ bs) ∗ H ∗ memRegion L 8 ∗
    ((L + 0x3f8#64) ↦₆₄ c0) ∗ memRegion (L + 0x578#64) 0x170 ∗
    memRegion (L + 0x6f0#64) 0x20 ∗ (A.pool ∗ R)
  have hmem4 : s.mem ⊨
      (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336 ∗
        ((L + 0x400#64) ↦₆₄ 0#64) ∗
        ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
        ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
        ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
        (x.out ↦₆₄ u0) ∗ ((x.out + 8#64) ↦₆₄ u1) ∗
        ((x.out + 0x10#64) ↦₆₄ u2) ∗ ((x.out + 0x18#64) ↦₆₄ u3) ∗
        memRegion (x.out + 0x20#64) 336 ∗
        stackAt L deserCalleeStack ∗
        deserSavedAtL_loopExit L s0) ∗ F := by
    dsimp only [F]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem3'
  intro hL
  have hwp := dexit_sepWP_loopExit_ext hmc_ok (s0 := s0) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
    hpc hrun hsp hal hx29 hx19 hx20 hw0 hrest hfr hsym hvregs
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hspf, htracef, hcsf, rfl⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hmem4 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hspf0 : sf.sp = s0.sp := by
    rw [hspf]
    dsimp [L, deserSpL]
    bv_omega
  refine ⟨sf, hsteps, Or.inl ⟨⟨hpcf, hspf0, hrunf⟩, ⟨hspf0, hcsf⟩, ?_⟩⟩
  have hmf1 : sf.mem ⊨
      ((x.p ↦ₛ bs) ∗
       ((x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ 8#64) ∗ ((x.out + 0x10#64) ↦₆₄ 0#64) ∗
         (((x.out + 0x18#64) ↦₆₄ w0) ∗ ((x.out + 0x20#64) ↦ₛ rest) ∗ H)) ∗
       (stackAt L deserCalleeStack ∗
        (memRegion L 8 ∗
          ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
          ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗
          ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
          ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
          memRegion (L + 0x578#64) 0x170 ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          memRegion (L + 0x6f0#64) 0x20 ∗
          deserSavedAtL_loopExit L s0))) ∗ (A.pool ∗ R) := by
    dsimp only [F, L] at hmf ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf
  have hout20 : x.out + 0x18#64 + 8#64 = x.out + 0x20#64 := by bv_omega
  have hss_out :
      ((x.out + 0x18#64) ↦₆₄ w0) ∗ ((x.out + 0x20#64) ↦ₛ rest) ∗ H ⊢
        prostSSGAt A (x.out + 0x18#64) v := by
    have hr := hrebuild (x.out + 0x18#64)
    rwa [hout20] at hr
  have hstk := dexit_frame_entails_stackAt_loopExit s0 c0 w0 rest hrest
  dsimp only at hstk
  have hmf2 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hss_out))) hstk))) hmf1
  unfold deserOutRawGA deserOutRecordGA
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htracef.trans htr, ?_⟩
  dsimp only [v, bs] at hmf2
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf2

theorem deserLoopExitG_ok_extWA
    (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hC : Stage2ContractsA img A ext)
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State) (hr : DeserializeScope x.r)
    (hs : DeserLoopGAtWA img A ext x R s0 (recFields x.r).length s) :
    DeserStepGAtWA img A ext x R s0 s (DeserRetGAtA img A x R s0) :=
  deserLoopExitG_ok_of_memcpyA img A ext (memcpy_ok_extWA hC) x R s0 s hr hs

/-! ## Relocatable `[LibsignalPlacement]` loop exit -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

theorem DLEGX_Placed : True := trivial

@[local simp, local wp_norm, local arm64_norm]
private theorem lscl_writeReg64 {pl : Obj.MultiPlacement} (s : State) (r : Reg) (v : BitVec 64) :
    LibsignalCodeLoaded pl (s.writeReg64 r v).mem = LibsignalCodeLoaded pl s.mem := rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem lscl_writeReg32 {pl : Obj.MultiPlacement} (s : State) (r : Reg) (v : BitVec 32) :
    LibsignalCodeLoaded pl (s.writeReg32 r v).mem = LibsignalCodeLoaded pl s.mem := rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem lscl_setPC {pl : Obj.MultiPlacement} (s : State) (pc : BitVec 64) :
    LibsignalCodeLoaded pl (s.setPC pc).mem = LibsignalCodeLoaded pl s.mem := rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem lscl_setPState {pl : Obj.MultiPlacement} (s : State) (ps : PState) :
    LibsignalCodeLoaded pl (s.setPState ps).mem = LibsignalCodeLoaded pl s.mem := rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem lscl_writeVReg128 {pl : Obj.MultiPlacement} (s : State) (idx : BitVec 5) (v : BitVec 128) :
    LibsignalCodeLoaded pl (s.writeVReg128 idx v).mem = LibsignalCodeLoaded pl s.mem := rfl

private theorem of_sepWP_lscl {pl : Obj.MultiPlacement} {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  ProofLib.SepWP.seq_frozen (fun _ _ h' hkf => h'.of_keepsFrozen hkf) hcl h

theorem memcpy_placed_ok_of_extHookStack [LibsignalPlacement] {H : LibsignalHooks}
    (hmc : subroutine_ok (lsProg_46 H) (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok (lsProg_46 H) (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec deserCalleeStack)) :=
  subroutine_ok_withLsCl_sessionMemcpySpec_mono (s2 := deserCalleeStack) (by decide) (by decide) hmc

theorem memcpy_placed_ok_extW [LibsignalPlacement] {H : LibsignalHooks}
    (hC : Stage2ContractsA0Placed H) :
    subroutine_ok (lsProg_46 H) (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec deserCalleeStack)) :=
  memcpy_placed_ok_of_extHookStack hC.memcpy

set_option maxHeartbeats 800000 in
/-- Relocatable `SessionRecord::deserialize` exit stepping (`+0x254` with `rem = 0` → `ret`) on
`lsProg_46 H` (Block `46`), discharging the four `memcpy` calls at `lsρ "memcpy"`. -/
theorem dexit_sepWP_placed_loopExit [LibsignalPlacement]
    {H : LibsignalHooks}
    (hmc_ok : subroutine_ok (lsProg_46 H) (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec deserCalleeStack)))
    {s0 s : State} {L out w0 u0 u1 u2 u3 : BitVec 64} {rest : List (BitVec 8)}
    (hpc : s.pc = (blkPl_46).base + 0x254#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = L)
    (hal : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = L + 0x710#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hw0 : w0 ≠ noneCap)
    (hrest : rest.length = 336)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (lsProg_46 H) (s0.readReg64 .lr) s
      (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336 ∗
        ((L + 0x400#64) ↦₆₄ 0#64) ∗
        ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
        ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
        ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
        (out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗
        ((out + 0x10#64) ↦₆₄ u2) ∗ ((out + 0x18#64) ↦₆₄ u3) ∗
        memRegion (out + 0x20#64) 336 ∗
        stackAt L deserCalleeStack ∗
        deserSavedAtL_loopExit L s0)
      (fun sf P_f =>
        sf.sp = L + 0x770#64 ∧
        sf.trace = s.trace ∧
        CalleeSavedPreserved s0 sf ∧
        P_f = (((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
          ((L + 0x400#64) ↦₆₄ 0#64) ∗
          ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
          ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗
          ((out + 0x10#64) ↦₆₄ 0#64) ∗ ((out + 0x18#64) ↦₆₄ w0) ∗
          ((out + 0x20#64) ↦ₛ rest) ∗
          stackAt L deserCalleeStack ∗
          deserSavedAtL_loopExit L s0)) := by
  subst hsp
  have hw0_ne := w0_add_one_ne_zero_loopExit hw0
  have hw0_beq := w0_add_one_beq_zero_loopExit hw0
  unfold deserSavedAtL_loopExit
  wp_steps
  wp_call hmc_ok (s.sp + 8#64, s.sp + 0x428#64, rest)
  wp_steps
  wp_call hmc_ok (s.sp + 0x2a8#64, s.sp + 8#64, rest)
  wp_steps
  wp_call hmc_ok (s.sp + 0x158#64, s.sp + 0x2a8#64, rest)
  apply of_sepWP_lscl (mid := lsρ "memcpy") (by assumption)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_c4
  wp_call hmc_ok (out + 0x20#64, s.sp + 0x158#64, rest)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]; ac_rfl

/-- Relocatable `SessionRecord::deserialize` loop exit (`+0x254` → `ret`) on `lsProg_46 H`,
parameterized by a `memcpy` contract at `deserCalleeStack`. -/
theorem deserLoopExitG_placed_ok_of_memcpy [LibsignalPlacement]
    (H : LibsignalHooks)
    (hmc_ok : subroutine_ok (lsProg_46 H) (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec deserCalleeStack)))
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State) (hr : DeserializeScope x.r)
    (hs : DeserLoopGPlacedW x R s0 (recFields x.r).length s) :
    DeserStepGPlacedW H x R s0 s
      (fun sf => Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
        (sf.mem ⊨ deserOutRawG x s0 sf ∗ R)) := by
  let _ := hr
  rcases hs with ⟨hpc, hrun, ⟨htr, hvregs⟩, hcrl, hsp, hal, hx29, hx19, hx20, _hx23, hmem⟩
  let L := deserSpL s0.sp
  let v := ssgAfter x.r (recFields x.r).length
  let bs := encodeRecord x.r
  have hmem : s.mem ⊨ deserLocalsG L x.p bs
      (((recFields x.r).drop (recFields x.r).length).flatMap GenField.enc) v ∗
    memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R := hmem
  rw [List.drop_length, List.flatMap_nil] at hmem
  unfold deserLocalsG at hmem
  rw [sliceCursorAfter_nil_loopExit L x.p bs, memRegion_3f8_split_loopExit L,
      deserSaved_eq_atL_loopExit s0] at hmem
  let c0 := x.p + BitVec.ofNat 64 bs.length
  have hmem1 : s.mem ⊨
      prostSSGAt A0 (L + 0x420#64) v ∗
      (memRegion x.out 368 ∗
       memRegion L 8 ∗
       (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗
         memRegion (L + 0x2a8#64) 336) ∗
       ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (x.p ↦ₛ bs) ∗
       ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
       memRegion (L + 0x578#64) 0x170 ∗
       ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20 ∗
       stackAt L deserCalleeStack ∗ deserSavedAtL_loopExit L s0 ∗ R) := by
    dsimp only [c0]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  obtain ⟨w0, rest, Hframe, hw0, hrest, hrebuild, hmem2⟩ := satisfies_prostSSGAt_move_loopExit hmem1
  have hmem3 : s.mem ⊨
      memRegion x.out 368 ∗
      (((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ Hframe ∗
       memRegion L 8 ∗
       (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗
         memRegion (L + 0x2a8#64) 336) ∗
       ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (x.p ↦ₛ bs) ∗
       ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
       memRegion (L + 0x578#64) 0x170 ∗
       ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20 ∗
       stackAt L deserCalleeStack ∗ deserSavedAtL_loopExit L s0 ∗ R) := by
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem2
  obtain ⟨u0, u1, u2, u3, hmem3'⟩ := satisfies_memRegion_out_split_loopExit hmem3
  let F := (x.p ↦ₛ bs) ∗ Hframe ∗ memRegion L 8 ∗
    ((L + 0x3f8#64) ↦₆₄ c0) ∗ memRegion (L + 0x578#64) 0x170 ∗
    memRegion (L + 0x6f0#64) 0x20 ∗ R
  have hmem4 : s.mem ⊨
      (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336 ∗
        ((L + 0x400#64) ↦₆₄ 0#64) ∗
        ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
        ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
        ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
        (x.out ↦₆₄ u0) ∗ ((x.out + 8#64) ↦₆₄ u1) ∗
        ((x.out + 0x10#64) ↦₆₄ u2) ∗ ((x.out + 0x18#64) ↦₆₄ u3) ∗
        memRegion (x.out + 0x20#64) 336 ∗
        stackAt L deserCalleeStack ∗
        deserSavedAtL_loopExit L s0) ∗ F := by
    dsimp only [F]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem3'
  intro hL
  have hwp := dexit_sepWP_placed_loopExit hmc_ok (s0 := s0) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
    hpc hrun hsp hal hx29 hx19 hx20 hw0 hrest hcrl.1 hvregs
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hspf, htracef, hcsf, rfl⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hmem4 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hspf0 : sf.sp = s0.sp := by
    rw [hspf]
    dsimp [L, deserSpL]
    bv_omega
  refine ⟨sf, hsteps, Or.inl ⟨⟨hpcf, hspf0, hrunf⟩, ⟨hspf0, hcsf⟩, ?_⟩⟩
  have hmf1 : sf.mem ⊨
      ((x.p ↦ₛ bs) ∗
       ((x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ 8#64) ∗ ((x.out + 0x10#64) ↦₆₄ 0#64) ∗
         (((x.out + 0x18#64) ↦₆₄ w0) ∗ ((x.out + 0x20#64) ↦ₛ rest) ∗ Hframe)) ∗
       (stackAt L deserCalleeStack ∗
        (memRegion L 8 ∗
          ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
          ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗
          ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
          ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
          memRegion (L + 0x578#64) 0x170 ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          memRegion (L + 0x6f0#64) 0x20 ∗
          deserSavedAtL_loopExit L s0))) ∗ R := by
    dsimp only [F, L] at hmf ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf
  have hout20 : x.out + 0x18#64 + 8#64 = x.out + 0x20#64 := by bv_omega
  have hss_out :
      ((x.out + 0x18#64) ↦₆₄ w0) ∗ ((x.out + 0x20#64) ↦ₛ rest) ∗ Hframe ⊢
        prostSSGAt A0 (x.out + 0x18#64) v := by
    have hr := hrebuild (x.out + 0x18#64)
    rwa [hout20] at hr
  have hstk := dexit_frame_entails_stackAt_loopExit s0 c0 w0 rest hrest
  dsimp only at hstk
  have hmf2 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hss_out))) hstk))) hmf1
  unfold deserOutRawG deserOutRecordG
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htracef.trans htr, ?_⟩
  dsimp only [v, bs] at hmf2
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf2

/-- Relocatable `SessionRecord::deserialize` loop exit (`+0x254` → `ret`) on `lsProg_46 H`,
discharged from `Stage2ContractsA0Placed H`. -/
theorem deserLoopExitG_placed_ok_extW [LibsignalPlacement]
    (H : LibsignalHooks)
    (hC : Stage2ContractsA0Placed H)
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State) (hr : DeserializeScope x.r)
    (hs : DeserLoopGPlacedW x R s0 (recFields x.r).length s) :
    DeserStepGPlacedW H x R s0 s
      (fun sf => Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
        (sf.mem ⊨ deserOutRawG x s0 sf ∗ R)) :=
  deserLoopExitG_placed_ok_of_memcpy H (memcpy_placed_ok_extW hC) x R s0 s hr hs

end Placed

end Proofs.libsignal.Hooks2

