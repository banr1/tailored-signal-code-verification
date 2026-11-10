/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopPeelDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.PrevBridge

/-!
# Decoded `SessionStructure` Inline Peel Proof

Proves `overPrevPeel_ok_ext` and `overPrevPeel_ok`, decomposing `prostSSGQAt A ss (ssgqOf sess)`
into `overPrevMovesSS ss w0 w1 w2 r1 r2 ∗ H` together with `w0.toNat < 2 ^ 63`, `r1.length = 304`,
`r2.length = 12`, and the drop-precondition reassembly `overPrevDropFromMovesExt A ss w0 w1 w2 r1 r2 H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Std Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral CryptoVerification.E2E.Record.L1GX
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ

private def RelocAt_peel (k n : Nat) (P : BitVec 64 → SepProp) : Prop :=
  ∀ a : BitVec 64, P a ⊢
    ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
      ⌜bs.length = n ∧ ∀ b : BitVec 64, (((b + BitVec.ofNat 64 k) ↦ₛ bs) ∗ H) ⊢ P b⌝ ∗
      ((a + BitVec.ofNat 64 k) ↦ₛ bs) ∗ H

private theorem relocAt_congr_peel {k n : Nat} {P Q : BitVec 64 → SepProp}
    (heq : ∀ a, Q a = P a) (hP : RelocAt_peel k n P) : RelocAt_peel k n Q := by
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

private theorem relocAt_pointsToBytes_peel (k : Nat) (off : BitVec 64) (bs : List (BitVec 8))
    {n : Nat} (hoff : off = BitVec.ofNat 64 k) (hn : bs.length = n) :
    RelocAt_peel k n (fun a => (a + off) ↦ₛ bs) := by
  subst hoff
  intro a
  refine Entails.sepExists_right bs (Entails.sepExists_right emp ?_)
  rw [sepConj_emp]
  refine Entails.pure_right ⟨hn, fun b => ?_⟩ (Entails.refl _)
  rw [sepConj_emp]
  exact Entails.refl _

private theorem relocAt_pointsTo32_peel (k : Nat) (off : BitVec 64) (w : BitVec 32)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_peel k 4 (fun a => (a + off) ↦₃₂ w) :=
  relocAt_congr_peel (fun a => pointsTo32_eq_pointsToBytes (a + off) w)
    (relocAt_pointsToBytes_peel k off (unpack32 w) hoff (unpack32_length w))

private theorem relocAt_pointsTo64_peel (k : Nat) (off : BitVec 64) (w : BitVec 64)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_peel k 8 (fun a => (a + off) ↦₆₄ w) :=
  relocAt_congr_peel (fun a => pointsTo64_eq_pointsToBytes (a + off) w)
    (relocAt_pointsToBytes_peel k off (unpack64 w) hoff (unpack64_length w))

private theorem relocAt_memRegion_peel (k : Nat) (off : BitVec 64) (n : Nat)
    (hoff : off = BitVec.ofNat 64 k) (hn : n ≤ 2 ^ 64) :
    RelocAt_peel k n (fun a => memRegion (a + off) n) := by
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

private theorem relocAt_const_right_peel {k n : Nat} {P : BitVec 64 → SepProp} (H0 : SepProp)
    (hP : RelocAt_peel k n P) :
    RelocAt_peel k n (fun a => P a ∗ H0) := by
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

private theorem relocAt_exists_peel {α : Type} {k n : Nat} {P : α → BitVec 64 → SepProp}
    (hP : ∀ x, RelocAt_peel k n (P x)) :
    RelocAt_peel k n (fun a => ∃∗ x : α, P x a) := by
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

private theorem bitVec_add_ofNat_add_peel (x : BitVec 64) (k n1 k2 : Nat) (hk : k + n1 = k2) :
    x + BitVec.ofNat 64 k + BitVec.ofNat 64 n1 = x + BitVec.ofNat 64 k2 := by
  subst hk
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem relocAt_sep_peel {k n1 k2 n2 : Nat} {P1 P2 : BitVec 64 → SepProp}
    (h1 : RelocAt_peel k n1 P1) (h2 : RelocAt_peel k2 n2 P2)
    (hk2 : k + n1 = k2) :
    RelocAt_peel k (n1 + n2) (fun a => P1 a ∗ P2 a) := by
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
  rw [pointsToBytes_append, hlen1, bitVec_add_ofNat_add_peel a k n1 k2 hk2]
  refine Entails.pure_right ⟨hlen, fun b => ?_⟩ (Entails.refl _)
  rw [pointsToBytes_append, hlen1, bitVec_add_ofNat_add_peel b k n1 k2 hk2]
  have hpull2 :
      ((((b + BitVec.ofNat 64 k) ↦ₛ bs1) ∗ ((b + BitVec.ofNat 64 k2) ↦ₛ bs2)) ∗ (H1 ∗ H2)) =
      ((((b + BitVec.ofNat 64 k) ↦ₛ bs1) ∗ H1) ∗ (((b + BitVec.ofNat 64 k2) ↦ₛ bs2) ∗ H2)) := by
    ac_rfl
  rw [hpull2]
  exact sepConj_mono (hrec1 b) (hrec2 b)

private theorem relocAt_zero_peel {n : Nat} {P : BitVec 64 → SepProp}
    (hP : RelocAt_peel 0 n (fun a => P (a + 0#64))) :
    RelocAt_peel 0 n P :=
  relocAt_congr_peel (fun a => congrArg P (BitVec.add_zero a).symm) hP

private theorem relocAt_shift_peel {k n : Nat} {P : BitVec 64 → SepProp} (off : BitVec 64)
    (hoff : off = BitVec.ofNat 64 k) (hP : RelocAt_peel 0 n P) :
    RelocAt_peel k n (fun a => P (a + off)) := by
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

private theorem relocAt_vecHeader_zero_peel (cap ptr len : BitVec 64) :
    RelocAt_peel 0 24 (fun a => vecHeader a cap ptr len) :=
  relocAt_sep_peel
    (relocAt_zero_peel (relocAt_pointsTo64_peel 0 0#64 cap rfl))
    (relocAt_sep_peel
      (relocAt_pointsTo64_peel 8 8#64 ptr rfl)
      (relocAt_pointsTo64_peel 16 16#64 len rfl) rfl) rfl

private theorem relocAt_vecHeader_peel (k : Nat) (off cap ptr len : BitVec 64)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_peel k 24 (fun a => vecHeader (a + off) cap ptr len) :=
  relocAt_shift_peel off hoff (relocAt_vecHeader_zero_peel cap ptr len)

private theorem relocAt_vecAt_peel {α : Type} (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (stride align : Nat) (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_peel k 24 (fun a => vecAt A stride align elem (a + off) cap ptr xs) :=
  relocAt_const_right_peel (vecBuf A stride align elem cap ptr xs)
    (relocAt_vecHeader_peel k off cap ptr (BitVec.ofNat 64 xs.length) hoff)

private theorem relocAt_vecOf_peel {α : Type} (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (stride align : Nat) (elem : α → BitVec 64 → SepProp) (xs : List α)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_peel k 24 (fun a => vecOf A stride align elem (a + off) xs) :=
  relocAt_exists_peel fun cap =>
    relocAt_exists_peel fun ptr =>
      relocAt_vecAt_peel k off A stride align elem cap ptr xs hoff

private def vecU8Heap_peel (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

private theorem relocAt_vecU8At_peel (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (cap ptr : BitVec 64) (bs : List (BitVec 8)) (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_peel k 24 (fun a => vecU8At A (a + off) cap ptr bs) :=
  relocAt_const_right_peel (vecU8Heap_peel A cap ptr bs)
    (relocAt_vecHeader_peel k off cap ptr (BitVec.ofNat 64 bs.length) hoff)

private theorem relocAt_vecU8_peel (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (bs : List (BitVec 8)) (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_peel k 24 (fun a => vecU8 A (a + off) bs) :=
  relocAt_exists_peel fun cap =>
    relocAt_exists_peel fun ptr =>
      relocAt_vecU8At_peel k off A cap ptr bs hoff

private theorem relocAt_vecU8_zero_peel (A : RustAlloc) (bs : List (BitVec 8)) :
    RelocAt_peel 0 24 (fun a => vecU8 A a bs) :=
  relocAt_zero_peel (relocAt_vecU8_peel 0 0#64 A bs rfl)

private theorem relocAt_prostChainGAt_zero_peel (A : RustAlloc) (c : ChainG) :
    RelocAt_peel 0 104 (fun a => prostChainGAt A a c) := by
  have hck : RelocAt_peel 0x48 32 (fun a =>
      match c.ck with
      | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
      | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
          memRegion (a + 0x64#64) 4) := by
    cases c.ck with
    | none =>
      exact relocAt_sep_peel
        (relocAt_pointsTo64_peel 0x48 0x48#64 noneCap rfl)
        (relocAt_memRegion_peel 0x50 0x50#64 24 rfl (by decide)) rfl
    | some ik =>
      rcases ik with ⟨i, k⟩
      exact relocAt_sep_peel (relocAt_vecU8_peel 0x48 0x48#64 A k rfl)
        (relocAt_sep_peel (relocAt_pointsTo32_peel 0x60 0x60#64 i rfl)
          (relocAt_memRegion_peel 0x64 0x64#64 4 rfl (by decide)) rfl) rfl
  exact relocAt_sep_peel (relocAt_vecU8_zero_peel A c.srk)
    (relocAt_sep_peel (relocAt_vecU8_peel 0x18 0x18#64 A c.priv rfl)
      (relocAt_sep_peel
        (relocAt_vecOf_peel 0x30 0x30#64 A 104 8 (fun mk b => prostMsgKeyAt A mk b) c.keys rfl)
        hck rfl) rfl) rfl

private theorem relocAt_pidAt_peel (pid : Option (BitVec 32)) (spkId : BitVec 32) :
    RelocAt_peel 0x110 24 (fun ss => pidAt ss pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
      ((ss + 0x120#64) ↦₃₂ spkId) ∗ memRegion (ss + 0x124#64) 4)) := by
  have hrest : RelocAt_peel 0x118 16 (fun ss => ((ss + 0x118#64) ↦₆₄ 0#64) ∗
      ((ss + 0x120#64) ↦₃₂ spkId) ∗ memRegion (ss + 0x124#64) 4) :=
    relocAt_sep_peel (relocAt_pointsTo64_peel 0x118 0x118#64 0#64 rfl)
      (relocAt_sep_peel (relocAt_pointsTo32_peel 0x120 0x120#64 spkId rfl)
        (relocAt_memRegion_peel 0x124 0x124#64 4 rfl (by decide)) rfl) rfl
  cases pid with
  | none =>
    exact relocAt_sep_peel (relocAt_pointsTo32_peel 0x110 0x110#64 0#32 rfl)
      (relocAt_sep_peel (relocAt_memRegion_peel 0x114 0x114#64 4 rfl (by decide)) hrest rfl) rfl
  | some i =>
    exact relocAt_sep_peel (relocAt_pointsTo32_peel 0x110 0x110#64 1#32 rfl)
      (relocAt_sep_peel (relocAt_pointsTo32_peel 0x114 0x114#64 i rfl) hrest rfl) rfl

private def prostSSGQMid304_peel (A : RustAlloc) (v : SSGQ) (ss : BitVec 64) : SepProp :=
  vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24

private theorem relocAt_prostSSGQMid304_peel (A : RustAlloc) (v : SSGQ) :
    RelocAt_peel 0x18 304 (prostSSGQMid304_peel A v) := by
  have hsender : RelocAt_peel 0x90 104 (fun ss =>
      match v.base.sender with
      | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
      | some c => prostChainGAt A (ss + 0x90#64) c) := by
    cases v.base.sender with
    | none =>
      exact relocAt_sep_peel
        (relocAt_pointsTo64_peel 0x90 0x90#64 noneCap rfl)
        (relocAt_memRegion_peel 0x98 0x98#64 96 rfl (by decide)) rfl
    | some c =>
      exact relocAt_shift_peel 0x90#64 rfl (relocAt_prostChainGAt_zero_peel A c)
  have hpending : RelocAt_peel 0xf8 48 (fun ss =>
      match v.base.pending with
      | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
      | some k => vecU8 A (ss + 0xf8#64) k ∗
          pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
            ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) := by
    cases v.base.pending with
    | none =>
      exact relocAt_sep_peel
        (relocAt_pointsTo64_peel 0xf8 0xf8#64 noneCap rfl)
        (relocAt_memRegion_peel 0x100 0x100#64 40 rfl (by decide)) rfl
    | some k =>
      exact relocAt_sep_peel (relocAt_vecU8_peel 0xf8 0xf8#64 A k rfl)
        (relocAt_pidAt_peel v.ext.pid v.ext.spkId) rfl
  have hkyberNone : RelocAt_peel 0x128 32 (fun ss =>
      ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24) :=
    relocAt_sep_peel
      (relocAt_pointsTo64_peel 0x128 0x128#64 noneCap rfl)
      (relocAt_memRegion_peel 0x130 0x130#64 24 rfl (by decide)) rfl
  exact relocAt_sep_peel (relocAt_vecU8_peel 0x18 0x18#64 A v.base.rik rfl)
    (relocAt_sep_peel (relocAt_vecU8_peel 0x30 0x30#64 A v.base.root rfl)
      (relocAt_sep_peel
        (relocAt_vecOf_peel 0x48 0x48#64 A 104 8 (fun c a => prostChainGAt A a c) v.base.recv rfl)
        (relocAt_sep_peel (relocAt_vecU8_peel 0x60 0x60#64 A v.ext.abk rfl)
          (relocAt_sep_peel (relocAt_vecU8_peel 0x78 0x78#64 A v.ext.pq rfl)
            (relocAt_sep_peel hsender
              (relocAt_sep_peel hpending hkyberNone rfl) rfl) rfl) rfl) rfl) rfl) rfl

private def prostSSGQTail12_peel (v : SSGQ) (ss : BitVec 64) : SepProp :=
  ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
    ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗
    ((ss + 0x154#64) ↦₃₂ v.ext.locReg)

private theorem relocAt_prostSSGQTail12_peel (v : SSGQ) :
    RelocAt_peel 0x14c 12 (prostSSGQTail12_peel v) :=
  relocAt_sep_peel (relocAt_pointsTo32_peel 0x14c 0x14c#64 v.base.prevCounter rfl)
    (relocAt_sep_peel (relocAt_pointsTo32_peel 0x150 0x150#64 v.ext.remReg rfl)
      (relocAt_pointsTo32_peel 0x154 0x154#64 v.ext.locReg rfl) rfl) rfl

private theorem vecU8Heap_w0_lt_peel (A : RustAlloc) (w0 ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8Heap_peel A w0 ptr bs ⊢ ⌜w0.toNat < 2 ^ 63⌝ ∗ vecU8Heap_peel A w0 ptr bs := by
  unfold vecU8Heap_peel
  apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
  exact Entails.pure_right hlt (Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _))

private theorem prostSSGQAt_eq_parts_peel (A : RustAlloc) (ss : BitVec 64) (v : SSGQ)
    (hkyber : v.ext.kyber = none) (hver : v.base.version = 4#32) :
    prostSSGQAt A ss v =
      vecU8 A ss v.base.lik ∗
      prostSSGQMid304_peel A v ss ∗
      ((ss + 0x148#64) ↦₃₂ 4#32) ∗
      prostSSGQTail12_peel v ss := by
  unfold prostSSGQAt prostSSGQMid304_peel prostSSGQTail12_peel
  rw [hkyber, hver]
  dsimp only [kyberAt]
  ac_rfl

/-- Proves `OverPrevPeelStmtExt A` for arbitrary `A : RustAlloc`. -/
theorem overPrevPeel_ok_ext (A : RustAlloc) : OverPrevPeelStmtExt A := by
  intro sess hQ hver hkyber ss
  have hkyb' : (ssgqOf sess).ext.kyber = none := by
    simp [ssgqOf, hkyber]
  have hver' : (ssgqOf sess).base.version = 4#32 := by
    simp [ssgqOf, ssgOf, hver]
  conv_lhs =>
    rw [prostSSGQAt_eq_parts_peel A ss (ssgqOf sess) hkyb' hver']
    dsimp only [vecU8]
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w0
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w1
  let w2 : BitVec 64 := BitVec.ofNat 64 (ssgqOf sess).base.lik.length
  have hvec :
      vecU8At A ss w0 w1 (ssgqOf sess).base.lik =
        (ss ↦₆₄ w0) ∗ ((ss + 8#64) ↦₆₄ w1) ∗ ((ss + 0x10#64) ↦₆₄ w2) ∗
          vecU8Heap_peel A w0 w1 (ssgqOf sess).base.lik := by
    unfold vecU8At vecHeader vecU8Heap_peel w2
    have h16 : (16#64 : BitVec 64) = 0x10#64 := rfl
    rw [h16]
    ac_rfl
  rw [hvec]
  refine Entails.trans
    (sepConj_mono_left
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_right
            (vecU8Heap_w0_lt_peel A w0 w1 (ssgqOf sess).base.lik))))) ?_
  have hpull0 :
      ((((ss ↦₆₄ w0) ∗ ((ss + 8#64) ↦₆₄ w1) ∗ ((ss + 0x10#64) ↦₆₄ w2) ∗
          (⌜w0.toNat < 2 ^ 63⌝ ∗ vecU8Heap_peel A w0 w1 (ssgqOf sess).base.lik)) ∗
        prostSSGQMid304_peel A (ssgqOf sess) ss ∗
        ((ss + 0x148#64) ↦₃₂ 4#32) ∗
        prostSSGQTail12_peel (ssgqOf sess) ss)) =
      (⌜w0.toNat < 2 ^ 63⌝ ∗
        ((ss ↦₆₄ w0) ∗ ((ss + 8#64) ↦₆₄ w1) ∗ ((ss + 0x10#64) ↦₆₄ w2) ∗
          vecU8Heap_peel A w0 w1 (ssgqOf sess).base.lik ∗
          prostSSGQMid304_peel A (ssgqOf sess) ss ∗
          ((ss + 0x148#64) ↦₃₂ 4#32) ∗
          prostSSGQTail12_peel (ssgqOf sess) ss)) := by ac_rfl
  rw [hpull0]
  apply Entails.pure_left; intro hw0
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono
              (relocAt_prostSSGQMid304_peel A (ssgqOf sess) ss)
              (sepConj_mono_right (relocAt_prostSSGQTail12_peel (ssgqOf sess) ss))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro r2
  apply Entails.sepExists_elim; intro H2
  apply Entails.sepExists_elim; intro r1
  apply Entails.sepExists_elim; intro H1
  have hpull1 :
      ((ss ↦₆₄ w0) ∗ ((ss + 8#64) ↦₆₄ w1) ∗ ((ss + 0x10#64) ↦₆₄ w2) ∗
        vecU8Heap_peel A w0 w1 (ssgqOf sess).base.lik ∗
        (⌜r1.length = 304 ∧
            ∀ b : BitVec 64, (((b + BitVec.ofNat 64 0x18) ↦ₛ r1) ∗ H1) ⊢
              prostSSGQMid304_peel A (ssgqOf sess) b⌝ ∗
          ((ss + BitVec.ofNat 64 0x18) ↦ₛ r1) ∗ H1) ∗
        ((ss + 0x148#64) ↦₃₂ 4#32) ∗
        (⌜r2.length = 12 ∧
            ∀ b : BitVec 64, (((b + BitVec.ofNat 64 0x14c) ↦ₛ r2) ∗ H2) ⊢
              prostSSGQTail12_peel (ssgqOf sess) b⌝ ∗
          ((ss + BitVec.ofNat 64 0x14c) ↦ₛ r2) ∗ H2)) =
      (⌜r1.length = 304 ∧
          ∀ b : BitVec 64, (((b + BitVec.ofNat 64 0x18) ↦ₛ r1) ∗ H1) ⊢
            prostSSGQMid304_peel A (ssgqOf sess) b⌝ ∗
        ⌜r2.length = 12 ∧
          ∀ b : BitVec 64, (((b + BitVec.ofNat 64 0x14c) ↦ₛ r2) ∗ H2) ⊢
            prostSSGQTail12_peel (ssgqOf sess) b⌝ ∗
        (overPrevMovesSS ss w0 w1 w2 r1 r2 ∗
          (vecU8Heap_peel A w0 w1 (ssgqOf sess).base.lik ∗ H1 ∗ H2))) := by
    unfold overPrevMovesSS
    have h18 : BitVec.ofNat 64 0x18 = 0x18#64 := rfl
    have h14c : BitVec.ofNat 64 0x14c = 0x14c#64 := rfl
    rw [h18, h14c]
    ac_rfl
  rw [hpull1]
  apply Entails.pure_left; rintro ⟨hr1_len, hr1_rec⟩
  apply Entails.pure_left; rintro ⟨hr2_len, hr2_rec⟩
  refine Entails.sepExists_right w0
    (Entails.sepExists_right w1
      (Entails.sepExists_right w2
        (Entails.sepExists_right r1
          (Entails.sepExists_right r2
            (Entails.sepExists_right (vecU8Heap_peel A w0 w1 (ssgqOf sess).base.lik ∗ H1 ∗ H2) ?_)))))
  rw [← sepConj_assoc (overPrevMovesSS ss w0 w1 w2 r1 r2)]
  refine Entails.pure_right ⟨hw0, hr1_len, hr2_len, ?_⟩ (Entails.refl _)
  unfold overPrevDropFromMovesExt
  refine Entails.trans ?_ (prevDec_dropPreA A sess hQ hver ss)
  rw [prostSSGQAt_eq_parts_peel A ss (ssgqOf sess) hkyb' hver']
  have hreb_eq :
      overPrevMovesSS ss w0 w1 w2 r1 r2 ∗
        (vecU8Heap_peel A w0 w1 (ssgqOf sess).base.lik ∗ H1 ∗ H2) =
      vecU8At A ss w0 w1 (ssgqOf sess).base.lik ∗
        (((ss + BitVec.ofNat 64 0x18) ↦ₛ r1) ∗ H1) ∗
        ((ss + 0x148#64) ↦₃₂ 4#32) ∗
        (((ss + BitVec.ofNat 64 0x14c) ↦ₛ r2) ∗ H2) := by
    unfold overPrevMovesSS
    rw [hvec]
    have h18 : BitVec.ofNat 64 0x18 = 0x18#64 := rfl
    have h14c : BitVec.ofNat 64 0x14c = 0x14c#64 := rfl
    rw [h18, h14c]
    ac_rfl
  rw [hreb_eq]
  have hvec_ent :
      vecU8At A ss w0 w1 (ssgqOf sess).base.lik ⊢ vecU8 A ss (ssgqOf sess).base.lik := by
    unfold vecU8
    exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.refl _))
  exact sepConj_mono hvec_ent
    (sepConj_mono (hr1_rec ss)
      (sepConj_mono (Entails.refl _) (hr2_rec ss)))

theorem overPrevPeel_ok : OverPrevPeelStmt :=
  overPrevPeel_ok_ext A0

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
