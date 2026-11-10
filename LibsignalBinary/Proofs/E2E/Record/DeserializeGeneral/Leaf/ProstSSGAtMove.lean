/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs

/-!
# 344-Byte Relocation Leaf (`prostSSGAt_move`) for `prostSSGAt`

Proves `prostSSGAt_move`, relocating `prostSSGAt A src v` across a 344-byte copy to `dst` and
showing word `0` (`lik` capacity) avoids the `Option` `None` niche.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ProstSSGAtMove

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession)

private def RelocAt_ssgmove (k n : Nat) (P : BitVec 64 → SepProp) : Prop :=
  ∀ a : BitVec 64, P a ⊢
    ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
      ⌜bs.length = n ∧ ∀ b : BitVec 64, (((b + BitVec.ofNat 64 k) ↦ₛ bs) ∗ H) ⊢ P b⌝ ∗
      ((a + BitVec.ofNat 64 k) ↦ₛ bs) ∗ H

private theorem relocAt_congr_ssgmove {k n : Nat} {P Q : BitVec 64 → SepProp}
    (heq : ∀ a, Q a = P a) (hP : RelocAt_ssgmove k n P) : RelocAt_ssgmove k n Q := by
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

private theorem relocAt_pointsToBytes_ssgmove (k : Nat) (off : BitVec 64) (bs : List (BitVec 8))
    {n : Nat} (hoff : off = BitVec.ofNat 64 k) (hn : bs.length = n) :
    RelocAt_ssgmove k n (fun a => (a + off) ↦ₛ bs) := by
  subst hoff
  intro a
  refine Entails.sepExists_right bs (Entails.sepExists_right emp ?_)
  rw [sepConj_emp]
  refine Entails.pure_right ⟨hn, fun b => ?_⟩ (Entails.refl _)
  rw [sepConj_emp]
  exact Entails.refl _

private theorem relocAt_pointsTo32_ssgmove (k : Nat) (off : BitVec 64) (w : BitVec 32)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_ssgmove k 4 (fun a => (a + off) ↦₃₂ w) :=
  relocAt_congr_ssgmove (fun a => pointsTo32_eq_pointsToBytes (a + off) w)
    (relocAt_pointsToBytes_ssgmove k off (unpack32 w) hoff (unpack32_length w))

private theorem relocAt_pointsTo64_ssgmove (k : Nat) (off : BitVec 64) (w : BitVec 64)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_ssgmove k 8 (fun a => (a + off) ↦₆₄ w) :=
  relocAt_congr_ssgmove (fun a => pointsTo64_eq_pointsToBytes (a + off) w)
    (relocAt_pointsToBytes_ssgmove k off (unpack64 w) hoff (unpack64_length w))

private theorem relocAt_memRegion_ssgmove (k : Nat) (off : BitVec 64) (n : Nat)
    (hoff : off = BitVec.ofNat 64 k) (hn : n ≤ 2 ^ 64) :
    RelocAt_ssgmove k n (fun a => memRegion (a + off) n) := by
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

private theorem relocAt_const_right_ssgmove {k n : Nat} {P : BitVec 64 → SepProp} (H0 : SepProp)
    (hP : RelocAt_ssgmove k n P) :
    RelocAt_ssgmove k n (fun a => P a ∗ H0) := by
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

private theorem relocAt_exists_ssgmove {α : Type} {k n : Nat} {P : α → BitVec 64 → SepProp}
    (hP : ∀ x, RelocAt_ssgmove k n (P x)) :
    RelocAt_ssgmove k n (fun a => ∃∗ x : α, P x a) := by
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

private theorem bitVec_add_ofNat_add_ssgmove (x : BitVec 64) (k n1 k2 : Nat) (hk : k + n1 = k2) :
    x + BitVec.ofNat 64 k + BitVec.ofNat 64 n1 = x + BitVec.ofNat 64 k2 := by
  subst hk
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem relocAt_sep_ssgmove {k n1 k2 n2 : Nat} {P1 P2 : BitVec 64 → SepProp}
    (h1 : RelocAt_ssgmove k n1 P1) (h2 : RelocAt_ssgmove k2 n2 P2)
    (hk2 : k + n1 = k2) :
    RelocAt_ssgmove k (n1 + n2) (fun a => P1 a ∗ P2 a) := by
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
  rw [pointsToBytes_append, hlen1, bitVec_add_ofNat_add_ssgmove a k n1 k2 hk2]
  refine Entails.pure_right ⟨hlen, fun b => ?_⟩ (Entails.refl _)
  rw [pointsToBytes_append, hlen1, bitVec_add_ofNat_add_ssgmove b k n1 k2 hk2]
  have hpull2 :
      ((((b + BitVec.ofNat 64 k) ↦ₛ bs1) ∗ ((b + BitVec.ofNat 64 k2) ↦ₛ bs2)) ∗ (H1 ∗ H2)) =
      ((((b + BitVec.ofNat 64 k) ↦ₛ bs1) ∗ H1) ∗ (((b + BitVec.ofNat 64 k2) ↦ₛ bs2) ∗ H2)) := by
    ac_rfl
  rw [hpull2]
  exact sepConj_mono (hrec1 b) (hrec2 b)

private theorem relocAt_zero_ssgmove {n : Nat} {P : BitVec 64 → SepProp}
    (hP : RelocAt_ssgmove 0 n (fun a => P (a + 0#64))) :
    RelocAt_ssgmove 0 n P :=
  relocAt_congr_ssgmove (fun a => congrArg P (BitVec.add_zero a).symm) hP

private theorem relocAt_shift_ssgmove {k n : Nat} {P : BitVec 64 → SepProp} (off : BitVec 64)
    (hoff : off = BitVec.ofNat 64 k) (hP : RelocAt_ssgmove 0 n P) :
    RelocAt_ssgmove k n (fun a => P (a + off)) := by
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

private theorem relocAt_vecHeader_zero_ssgmove (cap ptr len : BitVec 64) :
    RelocAt_ssgmove 0 24 (fun a => vecHeader a cap ptr len) :=
  relocAt_sep_ssgmove
    (relocAt_zero_ssgmove (relocAt_pointsTo64_ssgmove 0 0#64 cap rfl))
    (relocAt_sep_ssgmove
      (relocAt_pointsTo64_ssgmove 8 8#64 ptr rfl)
      (relocAt_pointsTo64_ssgmove 16 16#64 len rfl) rfl) rfl

private theorem relocAt_vecHeader_ssgmove (k : Nat) (off cap ptr len : BitVec 64)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_ssgmove k 24 (fun a => vecHeader (a + off) cap ptr len) :=
  relocAt_shift_ssgmove off hoff (relocAt_vecHeader_zero_ssgmove cap ptr len)

private theorem relocAt_vecAt_ssgmove {α : Type} (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (stride align : Nat) (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_ssgmove k 24 (fun a => vecAt A stride align elem (a + off) cap ptr xs) :=
  relocAt_const_right_ssgmove (vecBuf A stride align elem cap ptr xs)
    (relocAt_vecHeader_ssgmove k off cap ptr (BitVec.ofNat 64 xs.length) hoff)

private theorem relocAt_vecOf_ssgmove {α : Type} (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (stride align : Nat) (elem : α → BitVec 64 → SepProp) (xs : List α)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_ssgmove k 24 (fun a => vecOf A stride align elem (a + off) xs) :=
  relocAt_exists_ssgmove fun cap =>
    relocAt_exists_ssgmove fun ptr =>
      relocAt_vecAt_ssgmove k off A stride align elem cap ptr xs hoff

private def vecU8Heap_ssgmove (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

private theorem relocAt_vecU8At_ssgmove (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (cap ptr : BitVec 64) (bs : List (BitVec 8)) (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_ssgmove k 24 (fun a => vecU8At A (a + off) cap ptr bs) :=
  relocAt_const_right_ssgmove (vecU8Heap_ssgmove A cap ptr bs)
    (relocAt_vecHeader_ssgmove k off cap ptr (BitVec.ofNat 64 bs.length) hoff)

private theorem relocAt_vecU8_ssgmove (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (bs : List (BitVec 8)) (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_ssgmove k 24 (fun a => vecU8 A (a + off) bs) :=
  relocAt_exists_ssgmove fun cap =>
    relocAt_exists_ssgmove fun ptr =>
      relocAt_vecU8At_ssgmove k off A cap ptr bs hoff

private theorem relocAt_vecU8_zero_ssgmove (A : RustAlloc) (bs : List (BitVec 8)) :
    RelocAt_ssgmove 0 24 (fun a => vecU8 A a bs) :=
  relocAt_zero_ssgmove (relocAt_vecU8_ssgmove 0 0#64 A bs rfl)

private theorem relocAt_prostChainGAt_zero_ssgmove (A : RustAlloc) (c : ChainG) :
    RelocAt_ssgmove 0 104 (fun a => prostChainGAt A a c) := by
  have hck : RelocAt_ssgmove 0x48 32 (fun a =>
      match c.ck with
      | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
      | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
          memRegion (a + 0x64#64) 4) := by
    cases c.ck with
    | none =>
      exact relocAt_sep_ssgmove
        (relocAt_pointsTo64_ssgmove 0x48 0x48#64 noneCap rfl)
        (relocAt_memRegion_ssgmove 0x50 0x50#64 24 rfl (by decide)) rfl
    | some ik =>
      rcases ik with ⟨i, k⟩
      exact relocAt_sep_ssgmove (relocAt_vecU8_ssgmove 0x48 0x48#64 A k rfl)
        (relocAt_sep_ssgmove (relocAt_pointsTo32_ssgmove 0x60 0x60#64 i rfl)
          (relocAt_memRegion_ssgmove 0x64 0x64#64 4 rfl (by decide)) rfl) rfl
  exact relocAt_sep_ssgmove (relocAt_vecU8_zero_ssgmove A c.srk)
    (relocAt_sep_ssgmove (relocAt_vecU8_ssgmove 0x18 0x18#64 A c.priv rfl)
      (relocAt_sep_ssgmove
        (relocAt_vecOf_ssgmove 0x30 0x30#64 A 104 8 (fun mk b => prostMsgKeyAt A mk b) c.keys rfl)
        hck rfl) rfl) rfl

private def prostSSGAfterLik_ssgmove (A : RustAlloc) (v : SSG) (ss : BitVec 64) : SepProp :=
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

private theorem relocAt_prostSSGAfterLik_ssgmove (A : RustAlloc) (v : SSG) :
    RelocAt_ssgmove 0x18 320 (prostSSGAfterLik_ssgmove A v) := by
  have hsender : RelocAt_ssgmove 0x90 104 (fun ss =>
      match v.sender with
      | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
      | some c => prostChainGAt A (ss + 0x90#64) c) := by
    cases v.sender with
    | none =>
      exact relocAt_sep_ssgmove
        (relocAt_pointsTo64_ssgmove 0x90 0x90#64 noneCap rfl)
        (relocAt_memRegion_ssgmove 0x98 0x98#64 96 rfl (by decide)) rfl
    | some c =>
      exact relocAt_shift_ssgmove 0x90#64 rfl (relocAt_prostChainGAt_zero_ssgmove A c)
  have hpending : RelocAt_ssgmove 0xf8 48 (fun ss =>
      match v.pending with
      | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
      | some k => vecU8 A (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
          memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
          ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) := by
    cases v.pending with
    | none =>
      exact relocAt_sep_ssgmove
        (relocAt_pointsTo64_ssgmove 0xf8 0xf8#64 noneCap rfl)
        (relocAt_memRegion_ssgmove 0x100 0x100#64 40 rfl (by decide)) rfl
    | some k =>
      exact relocAt_sep_ssgmove (relocAt_vecU8_ssgmove 0xf8 0xf8#64 A k rfl)
        (relocAt_sep_ssgmove (relocAt_pointsTo32_ssgmove 0x110 0x110#64 0#32 rfl)
          (relocAt_sep_ssgmove (relocAt_memRegion_ssgmove 0x114 0x114#64 4 rfl (by decide))
            (relocAt_sep_ssgmove (relocAt_pointsTo64_ssgmove 0x118 0x118#64 0#64 rfl)
              (relocAt_sep_ssgmove (relocAt_pointsTo32_ssgmove 0x120 0x120#64 0#32 rfl)
                (relocAt_memRegion_ssgmove 0x124 0x124#64 4 rfl (by decide)) rfl)
              rfl) rfl) rfl) rfl
  exact relocAt_sep_ssgmove (relocAt_vecU8_ssgmove 0x18 0x18#64 A v.rik rfl)
    (relocAt_sep_ssgmove (relocAt_vecU8_ssgmove 0x30 0x30#64 A v.root rfl)
      (relocAt_sep_ssgmove
        (relocAt_vecOf_ssgmove 0x48 0x48#64 A 104 8 (fun c a => prostChainGAt A a c) v.recv rfl)
        (relocAt_sep_ssgmove (relocAt_vecU8_ssgmove 0x60 0x60#64 A [] rfl)
          (relocAt_sep_ssgmove (relocAt_vecU8_ssgmove 0x78 0x78#64 A [] rfl)
            (relocAt_sep_ssgmove hsender
              (relocAt_sep_ssgmove hpending
                (relocAt_sep_ssgmove (relocAt_pointsTo64_ssgmove 0x128 0x128#64 noneCap rfl)
                  (relocAt_sep_ssgmove (relocAt_memRegion_ssgmove 0x130 0x130#64 24 rfl (by decide))
                    (relocAt_sep_ssgmove (relocAt_pointsTo32_ssgmove 0x148 0x148#64 v.version rfl)
                      (relocAt_sep_ssgmove
                        (relocAt_pointsTo32_ssgmove 0x14c 0x14c#64 v.prevCounter rfl)
                        (relocAt_pointsTo64_ssgmove 0x150 0x150#64 0#64 rfl) rfl)
                      rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl

private def likTail_ssgmove (A : RustAlloc) (w0 ptr : BitVec 64) (lik : List (BitVec 8))
    (ss : BitVec 64) : SepProp :=
  (((ss + 8#64) ↦₆₄ ptr) ∗ ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 lik.length)) ∗
    vecU8Heap_ssgmove A w0 ptr lik

private theorem relocAt_likTail_ssgmove (A : RustAlloc) (w0 ptr : BitVec 64)
    (lik : List (BitVec 8)) :
    RelocAt_ssgmove 8 16 (likTail_ssgmove A w0 ptr lik) :=
  relocAt_const_right_ssgmove (vecU8Heap_ssgmove A w0 ptr lik)
    (relocAt_sep_ssgmove
      (relocAt_pointsTo64_ssgmove 8 8#64 ptr rfl)
      (relocAt_pointsTo64_ssgmove 16 16#64 (BitVec.ofNat 64 lik.length) rfl) rfl)

private def prostSSGTail_ssgmove (A : RustAlloc) (w0 ptr : BitVec 64) (v : SSG)
    (ss : BitVec 64) : SepProp :=
  likTail_ssgmove A w0 ptr v.lik ss ∗ prostSSGAfterLik_ssgmove A v ss

private theorem relocAt_prostSSGTail_ssgmove (A : RustAlloc) (w0 ptr : BitVec 64) (v : SSG) :
    RelocAt_ssgmove 8 336 (prostSSGTail_ssgmove A w0 ptr v) :=
  relocAt_sep_ssgmove (relocAt_likTail_ssgmove A w0 ptr v.lik)
    (relocAt_prostSSGAfterLik_ssgmove A v) rfl

private theorem vecU8At_eq_word0_sep_likTail_ssgmove (A : RustAlloc) (ss w0 ptr : BitVec 64)
    (lik : List (BitVec 8)) :
    vecU8At A ss w0 ptr lik = (ss ↦₆₄ w0) ∗ likTail_ssgmove A w0 ptr lik ss := by
  unfold vecU8At vecHeader likTail_ssgmove vecU8Heap_ssgmove
  ac_rfl

private theorem vecU8At_entails_vecU8_ssgmove (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢ vecU8 A v bs := by
  unfold vecU8
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

private theorem vecU8Heap_w0_ne_noneCap_ssgmove (A : RustAlloc) (w0 ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8Heap_ssgmove A w0 ptr bs ⊢ ⌜w0 ≠ noneCap⌝ ∗ vecU8Heap_ssgmove A w0 ptr bs := by
  unfold vecU8Heap_ssgmove
  apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
  have hne : w0 ≠ noneCap := by
    intro heq; subst heq; revert hlt; decide
  exact Entails.pure_right hne (Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _))

private theorem likTail_w0_ne_noneCap_ssgmove (A : RustAlloc) (w0 ptr : BitVec 64)
    (lik : List (BitVec 8)) (ss : BitVec 64) :
    likTail_ssgmove A w0 ptr lik ss ⊢ ⌜w0 ≠ noneCap⌝ ∗ likTail_ssgmove A w0 ptr lik ss := by
  unfold likTail_ssgmove
  refine Entails.trans (sepConj_mono_right (vecU8Heap_w0_ne_noneCap_ssgmove A w0 ptr lik)) ?_
  rw [sepConj_pure_left_comm]
  exact Entails.refl _

private theorem word0_sep_prostSSGTail_entails_prostSSGAt_ssgmove (A : RustAlloc)
    (b w0 ptr : BitVec 64) (v : SSG) :
    ((b ↦₆₄ w0) ∗ prostSSGTail_ssgmove A w0 ptr v b) ⊢ prostSSGAt A b v := by
  change ((b ↦₆₄ w0) ∗ (likTail_ssgmove A w0 ptr v.lik b ∗ prostSSGAfterLik_ssgmove A v b)) ⊢
    (vecU8 A b v.lik ∗ prostSSGAfterLik_ssgmove A v b)
  rw [← sepConj_assoc, ← vecU8At_eq_word0_sep_likTail_ssgmove]
  exact sepConj_mono_left (vecU8At_entails_vecU8_ssgmove A b w0 ptr v.lik)

theorem prostSSGAt_move (A : RustAlloc) (a : BitVec 64) (v : SSG) :
    prostSSGAt A a v ⊢
      ∃∗ w0 : BitVec 64, ∃∗ rest : List (BitVec 8), ∃∗ H : SepProp,
        ⌜w0 ≠ noneCap ∧ rest.length = 336 ∧
          ∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ rest) ∗ H) ⊢ prostSSGAt A b v⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ rest) ∗ H := by
  change (vecU8 A a v.lik ∗ prostSSGAfterLik_ssgmove A v a) ⊢ _
  unfold vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w0
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  rw [vecU8At_eq_word0_sep_likTail_ssgmove, sepConj_assoc]
  change ((a ↦₆₄ w0) ∗ prostSSGTail_ssgmove A w0 ptr v a) ⊢ _
  have hne_step :
      prostSSGTail_ssgmove A w0 ptr v a ⊢
        ⌜w0 ≠ noneCap⌝ ∗ prostSSGTail_ssgmove A w0 ptr v a := by
    unfold prostSSGTail_ssgmove
    refine Entails.trans (sepConj_mono_left (likTail_w0_ne_noneCap_ssgmove A w0 ptr v.lik a)) ?_
    rw [sepConj_assoc]
    exact Entails.refl _
  refine Entails.trans (sepConj_mono_right hne_step) ?_
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hw0
  refine Entails.trans (sepConj_mono_right (relocAt_prostSSGTail_ssgmove A w0 ptr v a)) ?_
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
    (word0_sep_prostSSGTail_entails_prostSSGAt_ssgmove A b w0 ptr v)

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ProstSSGAtMove
