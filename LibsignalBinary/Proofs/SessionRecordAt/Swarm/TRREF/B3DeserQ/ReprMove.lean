/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Fields
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push

/-!
# `Q`-Scope `SessionStructure` Relocation and Representation Bridges

Establishes byte-relocation of `prostSSGQAt` (`prostSSGQAt_move`, `satisfies_prostSSGQAt_moveA`)
and bridges a decoded `DeserializeScopeP_Q Q` `SessionStructure` to `sessionStateReprAt`,
`CanonRecord`, and `BinCanonSession` (`prostSSGQ_reprA`, `deserReprQA_ok`,
`deserOutRecordQA_entails_binCanonSession`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi CryptoGames.HMAC
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonCur CanonSession CanonChain
  CanonSender CanonPending)
open CryptoVerification.E2E.RecordX (DeserializeScopeP SessionScopeP)
open CryptoVerification.E2E.Bin (BinCanonSession)
open CryptoVerification.E2E.Record.L1GX
open Symbolic.Swarm.TRREF.B3Defs

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## `RelocAt` machinery and `prostSSGQAt_move` -/

private def RelocAt_qmove (k n : Nat) (P : BitVec 64 → SepProp) : Prop :=
  ∀ a : BitVec 64, P a ⊢
    ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
      ⌜bs.length = n ∧ ∀ b : BitVec 64, (((b + BitVec.ofNat 64 k) ↦ₛ bs) ∗ H) ⊢ P b⌝ ∗
      ((a + BitVec.ofNat 64 k) ↦ₛ bs) ∗ H

private theorem relocAt_congr_qmove {k n : Nat} {P Q : BitVec 64 → SepProp}
    (heq : ∀ a, Q a = P a) (hP : RelocAt_qmove k n P) : RelocAt_qmove k n Q := by
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

private theorem relocAt_pointsToBytes_qmove (k : Nat) (off : BitVec 64) (bs : List (BitVec 8))
    {n : Nat} (hoff : off = BitVec.ofNat 64 k) (hn : bs.length = n) :
    RelocAt_qmove k n (fun a => (a + off) ↦ₛ bs) := by
  subst hoff
  intro a
  refine Entails.sepExists_right bs (Entails.sepExists_right emp ?_)
  rw [sepConj_emp]
  refine Entails.pure_right ⟨hn, fun b => ?_⟩ (Entails.refl _)
  rw [sepConj_emp]
  exact Entails.refl _

private theorem relocAt_pointsTo32_qmove (k : Nat) (off : BitVec 64) (w : BitVec 32)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_qmove k 4 (fun a => (a + off) ↦₃₂ w) :=
  relocAt_congr_qmove (fun a => pointsTo32_eq_pointsToBytes (a + off) w)
    (relocAt_pointsToBytes_qmove k off (unpack32 w) hoff (unpack32_length w))

private theorem relocAt_pointsTo64_qmove (k : Nat) (off : BitVec 64) (w : BitVec 64)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_qmove k 8 (fun a => (a + off) ↦₆₄ w) :=
  relocAt_congr_qmove (fun a => pointsTo64_eq_pointsToBytes (a + off) w)
    (relocAt_pointsToBytes_qmove k off (unpack64 w) hoff (unpack64_length w))

private theorem relocAt_memRegion_qmove (k : Nat) (off : BitVec 64) (n : Nat)
    (hoff : off = BitVec.ofNat 64 k) (hn : n ≤ 2 ^ 64) :
    RelocAt_qmove k n (fun a => memRegion (a + off) n) := by
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

private theorem relocAt_const_right_qmove {k n : Nat} {P : BitVec 64 → SepProp} (H0 : SepProp)
    (hP : RelocAt_qmove k n P) :
    RelocAt_qmove k n (fun a => P a ∗ H0) := by
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

private theorem relocAt_exists_qmove {α : Type} {k n : Nat} {P : α → BitVec 64 → SepProp}
    (hP : ∀ x, RelocAt_qmove k n (P x)) :
    RelocAt_qmove k n (fun a => ∃∗ x : α, P x a) := by
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

private theorem bitVec_add_ofNat_add_qmove (x : BitVec 64) (k n1 k2 : Nat) (hk : k + n1 = k2) :
    x + BitVec.ofNat 64 k + BitVec.ofNat 64 n1 = x + BitVec.ofNat 64 k2 := by
  subst hk
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem relocAt_sep_qmove {k n1 k2 n2 : Nat} {P1 P2 : BitVec 64 → SepProp}
    (h1 : RelocAt_qmove k n1 P1) (h2 : RelocAt_qmove k2 n2 P2)
    (hk2 : k + n1 = k2) :
    RelocAt_qmove k (n1 + n2) (fun a => P1 a ∗ P2 a) := by
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
  rw [pointsToBytes_append, hlen1, bitVec_add_ofNat_add_qmove a k n1 k2 hk2]
  refine Entails.pure_right ⟨hlen, fun b => ?_⟩ (Entails.refl _)
  rw [pointsToBytes_append, hlen1, bitVec_add_ofNat_add_qmove b k n1 k2 hk2]
  have hpull2 :
      ((((b + BitVec.ofNat 64 k) ↦ₛ bs1) ∗ ((b + BitVec.ofNat 64 k2) ↦ₛ bs2)) ∗ (H1 ∗ H2)) =
      ((((b + BitVec.ofNat 64 k) ↦ₛ bs1) ∗ H1) ∗ (((b + BitVec.ofNat 64 k2) ↦ₛ bs2) ∗ H2)) := by
    ac_rfl
  rw [hpull2]
  exact sepConj_mono (hrec1 b) (hrec2 b)

private theorem relocAt_zero_qmove {n : Nat} {P : BitVec 64 → SepProp}
    (hP : RelocAt_qmove 0 n (fun a => P (a + 0#64))) :
    RelocAt_qmove 0 n P :=
  relocAt_congr_qmove (fun a => congrArg P (BitVec.add_zero a).symm) hP

private theorem relocAt_shift_qmove {k n : Nat} {P : BitVec 64 → SepProp} (off : BitVec 64)
    (hoff : off = BitVec.ofNat 64 k) (hP : RelocAt_qmove 0 n P) :
    RelocAt_qmove k n (fun a => P (a + off)) := by
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

private theorem relocAt_vecHeader_zero_qmove (cap ptr len : BitVec 64) :
    RelocAt_qmove 0 24 (fun a => vecHeader a cap ptr len) :=
  relocAt_sep_qmove
    (relocAt_zero_qmove (relocAt_pointsTo64_qmove 0 0#64 cap rfl))
    (relocAt_sep_qmove
      (relocAt_pointsTo64_qmove 8 8#64 ptr rfl)
      (relocAt_pointsTo64_qmove 16 16#64 len rfl) rfl) rfl

private theorem relocAt_vecHeader_qmove (k : Nat) (off cap ptr len : BitVec 64)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_qmove k 24 (fun a => vecHeader (a + off) cap ptr len) :=
  relocAt_shift_qmove off hoff (relocAt_vecHeader_zero_qmove cap ptr len)

private theorem relocAt_vecAt_qmove {α : Type} (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (stride align : Nat) (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_qmove k 24 (fun a => vecAt A stride align elem (a + off) cap ptr xs) :=
  relocAt_const_right_qmove (vecBuf A stride align elem cap ptr xs)
    (relocAt_vecHeader_qmove k off cap ptr (BitVec.ofNat 64 xs.length) hoff)

private theorem relocAt_vecOf_qmove {α : Type} (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (stride align : Nat) (elem : α → BitVec 64 → SepProp) (xs : List α)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_qmove k 24 (fun a => vecOf A stride align elem (a + off) xs) :=
  relocAt_exists_qmove fun cap =>
    relocAt_exists_qmove fun ptr =>
      relocAt_vecAt_qmove k off A stride align elem cap ptr xs hoff

private def vecU8Heap_qmove (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

private theorem relocAt_vecU8At_qmove (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (cap ptr : BitVec 64) (bs : List (BitVec 8)) (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_qmove k 24 (fun a => vecU8At A (a + off) cap ptr bs) :=
  relocAt_const_right_qmove (vecU8Heap_qmove A cap ptr bs)
    (relocAt_vecHeader_qmove k off cap ptr (BitVec.ofNat 64 bs.length) hoff)

private theorem relocAt_vecU8_qmove (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (bs : List (BitVec 8)) (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_qmove k 24 (fun a => vecU8 A (a + off) bs) :=
  relocAt_exists_qmove fun cap =>
    relocAt_exists_qmove fun ptr =>
      relocAt_vecU8At_qmove k off A cap ptr bs hoff

private theorem relocAt_vecU8_zero_qmove (A : RustAlloc) (bs : List (BitVec 8)) :
    RelocAt_qmove 0 24 (fun a => vecU8 A a bs) :=
  relocAt_zero_qmove (relocAt_vecU8_qmove 0 0#64 A bs rfl)

private theorem relocAt_prostChainGAt_zero_qmove (A : RustAlloc) (c : ChainG) :
    RelocAt_qmove 0 104 (fun a => prostChainGAt A a c) := by
  have hck : RelocAt_qmove 0x48 32 (fun a =>
      match c.ck with
      | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
      | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
          memRegion (a + 0x64#64) 4) := by
    cases c.ck with
    | none =>
      exact relocAt_sep_qmove
        (relocAt_pointsTo64_qmove 0x48 0x48#64 noneCap rfl)
        (relocAt_memRegion_qmove 0x50 0x50#64 24 rfl (by decide)) rfl
    | some ik =>
      rcases ik with ⟨i, k⟩
      exact relocAt_sep_qmove (relocAt_vecU8_qmove 0x48 0x48#64 A k rfl)
        (relocAt_sep_qmove (relocAt_pointsTo32_qmove 0x60 0x60#64 i rfl)
          (relocAt_memRegion_qmove 0x64 0x64#64 4 rfl (by decide)) rfl) rfl
  exact relocAt_sep_qmove (relocAt_vecU8_zero_qmove A c.srk)
    (relocAt_sep_qmove (relocAt_vecU8_qmove 0x18 0x18#64 A c.priv rfl)
      (relocAt_sep_qmove
        (relocAt_vecOf_qmove 0x30 0x30#64 A 104 8 (fun mk b => prostMsgKeyAt A mk b) c.keys rfl)
        hck rfl) rfl) rfl

private theorem relocAt_pidAt_qmove (pid : Option (BitVec 32)) (spkId : BitVec 32) :
    RelocAt_qmove 0x110 24 (fun ss => pidAt ss pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
      ((ss + 0x120#64) ↦₃₂ spkId) ∗ memRegion (ss + 0x124#64) 4)) := by
  have hrest : RelocAt_qmove 0x118 16 (fun ss => ((ss + 0x118#64) ↦₆₄ 0#64) ∗
      ((ss + 0x120#64) ↦₃₂ spkId) ∗ memRegion (ss + 0x124#64) 4) :=
    relocAt_sep_qmove (relocAt_pointsTo64_qmove 0x118 0x118#64 0#64 rfl)
      (relocAt_sep_qmove (relocAt_pointsTo32_qmove 0x120 0x120#64 spkId rfl)
        (relocAt_memRegion_qmove 0x124 0x124#64 4 rfl (by decide)) rfl) rfl
  cases pid with
  | none =>
    exact relocAt_sep_qmove (relocAt_pointsTo32_qmove 0x110 0x110#64 0#32 rfl)
      (relocAt_sep_qmove (relocAt_memRegion_qmove 0x114 0x114#64 4 rfl (by decide)) hrest rfl) rfl
  | some i =>
    exact relocAt_sep_qmove (relocAt_pointsTo32_qmove 0x110 0x110#64 1#32 rfl)
      (relocAt_sep_qmove (relocAt_pointsTo32_qmove 0x114 0x114#64 i rfl) hrest rfl) rfl

private theorem relocAt_kyberAt_qmove (A : RustAlloc) (kyber : Option (BitVec 32 × List (BitVec 8)))
    (v : SSGQ) :
    RelocAt_qmove 0x128 48 (fun ss => kyberAt A ss kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))) := by
  have hrest : RelocAt_qmove 0x148 16 (fun ss =>
      ((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg)) :=
    relocAt_sep_qmove (relocAt_pointsTo32_qmove 0x148 0x148#64 v.base.version rfl)
      (relocAt_sep_qmove (relocAt_pointsTo32_qmove 0x14c 0x14c#64 v.base.prevCounter rfl)
        (relocAt_sep_qmove (relocAt_pointsTo32_qmove 0x150 0x150#64 v.ext.remReg rfl)
          (relocAt_pointsTo32_qmove 0x154 0x154#64 v.ext.locReg rfl) rfl) rfl) rfl
  cases kyber with
  | none =>
    exact relocAt_sep_qmove (relocAt_pointsTo64_qmove 0x128 0x128#64 noneCap rfl)
      (relocAt_sep_qmove (relocAt_memRegion_qmove 0x130 0x130#64 24 rfl (by decide)) hrest rfl) rfl
  | some ik =>
    rcases ik with ⟨i, ct⟩
    exact relocAt_sep_qmove (relocAt_vecU8_qmove 0x128 0x128#64 A ct rfl)
      (relocAt_sep_qmove (relocAt_pointsTo32_qmove 0x140 0x140#64 i rfl)
        (relocAt_sep_qmove (relocAt_memRegion_qmove 0x144 0x144#64 4 rfl (by decide)) hrest rfl)
        rfl) rfl

private def prostSSGQAfterLik_qmove (A : RustAlloc) (v : SSGQ) (ss : BitVec 64) : SepProp :=
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
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

private theorem relocAt_prostSSGQAfterLik_qmove (A : RustAlloc) (v : SSGQ) :
    RelocAt_qmove 0x18 320 (prostSSGQAfterLik_qmove A v) := by
  have hsender : RelocAt_qmove 0x90 104 (fun ss =>
      match v.base.sender with
      | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
      | some c => prostChainGAt A (ss + 0x90#64) c) := by
    cases v.base.sender with
    | none =>
      exact relocAt_sep_qmove
        (relocAt_pointsTo64_qmove 0x90 0x90#64 noneCap rfl)
        (relocAt_memRegion_qmove 0x98 0x98#64 96 rfl (by decide)) rfl
    | some c =>
      exact relocAt_shift_qmove 0x90#64 rfl (relocAt_prostChainGAt_zero_qmove A c)
  have hpending : RelocAt_qmove 0xf8 48 (fun ss =>
      match v.base.pending with
      | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
      | some k => vecU8 A (ss + 0xf8#64) k ∗
          pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
            ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) := by
    cases v.base.pending with
    | none =>
      exact relocAt_sep_qmove
        (relocAt_pointsTo64_qmove 0xf8 0xf8#64 noneCap rfl)
        (relocAt_memRegion_qmove 0x100 0x100#64 40 rfl (by decide)) rfl
    | some k =>
      exact relocAt_sep_qmove (relocAt_vecU8_qmove 0xf8 0xf8#64 A k rfl)
        (relocAt_pidAt_qmove v.ext.pid v.ext.spkId) rfl
  exact relocAt_sep_qmove (relocAt_vecU8_qmove 0x18 0x18#64 A v.base.rik rfl)
    (relocAt_sep_qmove (relocAt_vecU8_qmove 0x30 0x30#64 A v.base.root rfl)
      (relocAt_sep_qmove
        (relocAt_vecOf_qmove 0x48 0x48#64 A 104 8 (fun c a => prostChainGAt A a c) v.base.recv rfl)
        (relocAt_sep_qmove (relocAt_vecU8_qmove 0x60 0x60#64 A v.ext.abk rfl)
          (relocAt_sep_qmove (relocAt_vecU8_qmove 0x78 0x78#64 A v.ext.pq rfl)
            (relocAt_sep_qmove hsender
              (relocAt_sep_qmove hpending
                (relocAt_kyberAt_qmove A v.ext.kyber v) rfl) rfl) rfl) rfl) rfl) rfl) rfl

private def likTail_qmove (A : RustAlloc) (w0 ptr : BitVec 64) (lik : List (BitVec 8))
    (ss : BitVec 64) : SepProp :=
  (((ss + 8#64) ↦₆₄ ptr) ∗ ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 lik.length)) ∗
    vecU8Heap_qmove A w0 ptr lik

private theorem relocAt_likTail_qmove (A : RustAlloc) (w0 ptr : BitVec 64)
    (lik : List (BitVec 8)) :
    RelocAt_qmove 8 16 (likTail_qmove A w0 ptr lik) :=
  relocAt_const_right_qmove (vecU8Heap_qmove A w0 ptr lik)
    (relocAt_sep_qmove
      (relocAt_pointsTo64_qmove 8 8#64 ptr rfl)
      (relocAt_pointsTo64_qmove 16 16#64 (BitVec.ofNat 64 lik.length) rfl) rfl)

private def prostSSGQTail_qmove (A : RustAlloc) (w0 ptr : BitVec 64) (v : SSGQ)
    (ss : BitVec 64) : SepProp :=
  likTail_qmove A w0 ptr v.base.lik ss ∗ prostSSGQAfterLik_qmove A v ss

private theorem relocAt_prostSSGQTail_qmove (A : RustAlloc) (w0 ptr : BitVec 64) (v : SSGQ) :
    RelocAt_qmove 8 336 (prostSSGQTail_qmove A w0 ptr v) :=
  relocAt_sep_qmove (relocAt_likTail_qmove A w0 ptr v.base.lik)
    (relocAt_prostSSGQAfterLik_qmove A v) rfl

private theorem vecU8At_eq_word0_sep_likTail_qmove (A : RustAlloc) (ss w0 ptr : BitVec 64)
    (lik : List (BitVec 8)) :
    vecU8At A ss w0 ptr lik = (ss ↦₆₄ w0) ∗ likTail_qmove A w0 ptr lik ss := by
  unfold vecU8At vecHeader likTail_qmove vecU8Heap_qmove
  ac_rfl

private theorem vecU8At_entails_vecU8_qmove (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢ vecU8 A v bs := by
  unfold vecU8
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

private theorem vecU8Heap_w0_ne_noneCap_qmove (A : RustAlloc) (w0 ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8Heap_qmove A w0 ptr bs ⊢ ⌜w0 ≠ noneCap⌝ ∗ vecU8Heap_qmove A w0 ptr bs := by
  unfold vecU8Heap_qmove
  apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
  have hne : w0 ≠ noneCap := by
    intro heq; subst heq; revert hlt; decide
  exact Entails.pure_right hne (Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _))

private theorem likTail_w0_ne_noneCap_qmove (A : RustAlloc) (w0 ptr : BitVec 64)
    (lik : List (BitVec 8)) (ss : BitVec 64) :
    likTail_qmove A w0 ptr lik ss ⊢ ⌜w0 ≠ noneCap⌝ ∗ likTail_qmove A w0 ptr lik ss := by
  unfold likTail_qmove
  refine Entails.trans (sepConj_mono_right (vecU8Heap_w0_ne_noneCap_qmove A w0 ptr lik)) ?_
  rw [sepConj_pure_left_comm]
  exact Entails.refl _

private theorem word0_sep_prostSSGQTail_entails_prostSSGQAt_qmove (A : RustAlloc)
    (b w0 ptr : BitVec 64) (v : SSGQ) :
    ((b ↦₆₄ w0) ∗ prostSSGQTail_qmove A w0 ptr v b) ⊢ prostSSGQAt A b v := by
  change ((b ↦₆₄ w0) ∗ (likTail_qmove A w0 ptr v.base.lik b ∗ prostSSGQAfterLik_qmove A v b)) ⊢
    (vecU8 A b v.base.lik ∗ prostSSGQAfterLik_qmove A v b)
  rw [← sepConj_assoc, ← vecU8At_eq_word0_sep_likTail_qmove]
  exact sepConj_mono_left (vecU8At_entails_vecU8_qmove A b w0 ptr v.base.lik)

/-- `prostSSGQAt` is relocatable (344 bytes = 8-byte word 0 `w0 ≠ noneCap` + 336-byte `rest` +
heap frame `H`). -/
theorem prostSSGQAt_move (A : RustAlloc) (a : BitVec 64) (v : SSGQ) :
    prostSSGQAt A a v ⊢
      ∃∗ w0 : BitVec 64, ∃∗ rest : List (BitVec 8), ∃∗ H : SepProp,
        ⌜w0 ≠ noneCap ∧ rest.length = 336 ∧
          ∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ rest) ∗ H) ⊢ prostSSGQAt A b v⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ rest) ∗ H := by
  change (vecU8 A a v.base.lik ∗ prostSSGQAfterLik_qmove A v a) ⊢ _
  unfold vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w0
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  rw [vecU8At_eq_word0_sep_likTail_qmove, sepConj_assoc]
  change ((a ↦₆₄ w0) ∗ prostSSGQTail_qmove A w0 ptr v a) ⊢ _
  have hne_step :
      prostSSGQTail_qmove A w0 ptr v a ⊢
        ⌜w0 ≠ noneCap⌝ ∗ prostSSGQTail_qmove A w0 ptr v a := by
    unfold prostSSGQTail_qmove
    refine Entails.trans (sepConj_mono_left (likTail_w0_ne_noneCap_qmove A w0 ptr v.base.lik a)) ?_
    rw [sepConj_assoc]
    exact Entails.refl _
  refine Entails.trans (sepConj_mono_right hne_step) ?_
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hw0
  refine Entails.trans (sepConj_mono_right (relocAt_prostSSGQTail_qmove A w0 ptr v a)) ?_
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
    (word0_sep_prostSSGQTail_entails_prostSSGQAt_qmove A b w0 ptr v)

/-- `Satisfies`-level unpacking of `prostSSGQAt_move` at `L + 0x420#64` for `DeserLoopExitQ` (`A : RustAlloc`). -/
theorem satisfies_prostSSGQAt_moveA {A : RustAlloc} {m : Memory} {L : BitVec 64} {v : SSGQ} {R : SepProp}
    (h : m ⊨ prostSSGQAt A (L + 0x420#64) v ∗ R) :
    ∃ w0 : BitVec 64, ∃ rest : List (BitVec 8), ∃ H : SepProp,
      w0 ≠ noneCap ∧ rest.length = 336 ∧
      (∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ rest) ∗ H) ⊢ prostSSGQAt A b v) ∧
      (m ⊨ (((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ H) ∗ R) := by
  have h428 : L + 0x420#64 + 8#64 = L + 0x428#64 := by bv_omega
  have hmove_ent := prostSSGQAt_move A (L + 0x420#64) v
  rw [h428] at hmove_ent
  have h1 := Satisfies.mono (sepConj_mono_left hmove_ent) h
  simp only [sepExists_sepConj_left, satisfies_sepExists] at h1
  rcases h1 with ⟨w0, rest, H, h1⟩
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hw0, hrest, hrebuild⟩, h1⟩
  exact ⟨w0, rest, H, hw0, hrest, hrebuild, by simpa only [sepConj_assoc] using h1⟩

theorem satisfies_prostSSGQAt_move {m : Memory} {L : BitVec 64} {v : SSGQ} {R : SepProp}
    (h : m ⊨ prostSSGQAt A0 (L + 0x420#64) v ∗ R) :
    ∃ w0 : BitVec 64, ∃ rest : List (BitVec 8), ∃ H : SepProp,
      w0 ≠ noneCap ∧ rest.length = 336 ∧
      (∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ rest) ∗ H) ⊢ prostSSGQAt A0 b v) ∧
      (m ⊨ (((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ H) ∗ R) :=
  satisfies_prostSSGQAt_moveA h

/-! ## `SessionStructure` representation bridge (`prostSSGQ_reprA`) -/

private theorem deserialize_serialize_pk_qrepr (pk : PublicKey) :
    PublicKey.deserialize pk.serialize = .ok pk := by
  unfold PublicKey.serialize PublicKey.deserialize
  rcases pk with ⟨⟨bs, hbs⟩⟩
  simp [hbs]
  congr 1
  exact Subtype.ext (List.take_of_length_le (Nat.le_of_eq hbs))

private theorem serialize_pk_length_qrepr (pk : PublicKey) :
    pk.serialize.length = 33 := by
  unfold PublicKey.serialize
  simp [pk.bytes.toList_length]

private theorem serialize_ik_length_qrepr (ik : IdentityKey) :
    ik.serialize.length = 33 :=
  serialize_pk_length_qrepr ik.publicKey

private theorem arrayAt_map_entails_zip_qrepr {α β γ : Type}
    (elem1 : β → BitVec 64 → SepProp) (elem2 : γ × α → BitVec 64 → SepProp)
    (P : γ × α → Prop) (f : α → β) (stride : Nat) :
    ∀ (xs : List α) (base : BitVec 64),
      (∀ x ∈ xs, ∀ b : BitVec 64, elem1 (f x) b ⊢ ∃∗ g : γ, ⌜P (g, x)⌝ ∗ elem2 (g, x) b) →
      arrayAt elem1 stride base (xs.map f) ⊢
        ∃∗ gs : List γ,
          ⌜gs.length = xs.length ∧ (∀ gx ∈ gs.zip xs, P gx)⌝ ∗
            arrayAt elem2 stride base (gs.zip xs)
  | [], base, _ => by
    dsimp only [List.map, arrayAt]
    refine Entails.sepExists_right [] ?_
    have hall : ∀ gx ∈ ([] : List γ).zip ([] : List α), P gx := by
      intro _ h; cases h
    exact Entails.pure_right ⟨rfl, hall⟩ (Entails.refl _)
  | x :: xs, base, h => by
    dsimp only [List.map, arrayAt]
    have hx := h x List.mem_cons_self base
    have hxs := arrayAt_map_entails_zip_qrepr elem1 elem2 P f stride xs
      (base + BitVec.ofNat 64 stride) (fun y hy b => h y (List.mem_cons_of_mem x hy) b)
    refine Entails.trans (sepConj_mono hx hxs) ?_
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro gs
    apply Entails.sepExists_elim; intro g
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hpx
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hlen, hpz⟩
    refine Entails.sepExists_right (g :: gs) ?_
    have hlen' : (g :: gs).length = (x :: xs).length := by simp [hlen]
    have hpz' : ∀ gx ∈ (g :: gs).zip (x :: xs), P gx := by
      intro gx hgx
      simp only [List.zip_cons_cons, List.mem_cons] at hgx
      rcases hgx with rfl | hgx
      · exact hpx
      · exact hpz gx hgx
    refine Entails.pure_right ⟨hlen', hpz'⟩ ?_
    dsimp only [List.zip_cons_cons, arrayAt]
    exact Entails.refl _

private theorem vecAt_map_entails_zip_qrepr {α β γ : Type} (A : RustAlloc)
    (stride align : Nat) (elem1 : β → BitVec 64 → SepProp) (elem2 : γ × α → BitVec 64 → SepProp)
    (P : γ × α → Prop) (f : α → β) (v cap ptr : BitVec 64) (xs : List α)
    (h : ∀ x ∈ xs, ∀ b : BitVec 64, elem1 (f x) b ⊢ ∃∗ g : γ, ⌜P (g, x)⌝ ∗ elem2 (g, x) b) :
    vecAt A stride align elem1 v cap ptr (xs.map f) ⊢
      ∃∗ gs : List γ,
        ⌜gs.length = xs.length ∧ (∀ gx ∈ gs.zip xs, P gx)⌝ ∗
          vecAt A stride align elem2 v cap ptr (gs.zip xs) := by
  unfold vecAt vecBuf
  rw [List.length_map]
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hbuf
  by_cases hcap : cap = 0
  · subst hcap
    have hxs0 : xs.length = 0 := Nat.eq_zero_of_le_zero hbuf.1
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero hxs0
    subst hnil
    refine Entails.sepExists_right [] ?_
    have hall : ∀ gx ∈ ([] : List γ).zip ([] : List α), P gx := by intro _ h; cases h
    refine Entails.pure_right ⟨rfl, hall⟩ ?_
    rw [sepConj_pure_left_comm]
    exact Entails.pure_right hbuf (Entails.refl _)
  · simp only [hcap, ↓reduceIte]
    have harr := arrayAt_map_entails_zip_qrepr elem1 elem2 P f stride xs ptr h
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left harr))) ?_
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro gs
    rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hlen, hpz⟩
    refine Entails.sepExists_right gs ?_
    refine Entails.pure_right ⟨hlen, hpz⟩ ?_
    have hzip_len : (gs.zip xs).length = xs.length := by
      rw [List.length_zip, hlen, Nat.min_self]
    rw [hzip_len]
    rw [sepConj_pure_left_comm]
    exact Entails.pure_right hbuf (Entails.refl _)

private theorem vecOf_map_entails_vecAt_zip_qrepr {α β γ : Type} (A : RustAlloc)
    (stride align : Nat) (elem1 : β → BitVec 64 → SepProp) (elem2 : γ × α → BitVec 64 → SepProp)
    (P : γ × α → Prop) (f : α → β) (v : BitVec 64) (xs : List α)
    (h : ∀ x ∈ xs, ∀ b : BitVec 64, elem1 (f x) b ⊢ ∃∗ g : γ, ⌜P (g, x)⌝ ∗ elem2 (g, x) b) :
    vecOf A stride align elem1 v (xs.map f) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ gs : List γ,
        ⌜gs.length = xs.length ∧ (∀ gx ∈ gs.zip xs, P gx)⌝ ∗
          vecAt A stride align elem2 v cap ptr (gs.zip xs) := by
  unfold vecOf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap ?_
  refine Entails.sepExists_right ptr ?_
  exact vecAt_map_entails_zip_qrepr A stride align elem1 elem2 P f v cap ptr xs h

private theorem prostMsgKeyAt_entails_messageKeyAt_qrepr (A : RustAlloc) (mk : MessageKeyGenerator)
    (hseed : mk.seed.length = 32) (a : BitVec 64) :
    prostMsgKeyAt A mk a ⊢
      ∃∗ mg : MessageKeyGhost, ⌜True⌝ ∗ messageKeyAt A (mg, mk) a := by
  have hne : mk.seed ≠ [] := by
    intro h; rw [h] at hseed; cases hseed
  unfold prostMsgKeyAt vecU8
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro seedCap
  apply Entails.sepExists_elim; intro seedPtr
  apply Entails.sepExists_elim; intro ivCap
  apply Entails.sepExists_elim; intro ivPtr
  apply Entails.sepExists_elim; intro macCap
  apply Entails.sepExists_elim; intro macPtr
  apply Entails.sepExists_elim; intro cipherCap
  apply Entails.sepExists_elim; intro cipherPtr
  let mg : MessageKeyGhost := {
    cipher := ⟨cipherCap, cipherPtr⟩
    mac := ⟨macCap, macPtr⟩
    iv := ⟨ivCap, ivPtr⟩
    seed := ⟨seedCap, seedPtr⟩
  }
  refine Entails.sepExists_right mg ?_
  refine Entails.pure_right trivial ?_
  unfold messageKeyAt
  exact Entails.pure_right hne (Entails.refl _)

private theorem prostChainKey_entails_optChainKeyAt_qrepr (A : RustAlloc) (o : Option ChainKey) (a : BitVec 64) :
    (match o.map (fun ck => (ck.index, HMAC.keyToBytes32 ck.key)) with
     | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
     | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
         memRegion (a + 0x64#64) 4) ⊢
      ∃∗ ckPin : VecPin, optChainKeyAt A ckPin o (a + 72#64) := by
  rcases o with _ | ck
  · dsimp only [Option.map, optChainKeyAt]
    refine Entails.sepExists_right ⟨0, 0⟩ ?_
    have ha : a + 72#64 + 8#64 = a + 0x50#64 := by rw [BitVec.add_assoc]; rfl
    rw [ha]
    exact Entails.refl _
  · dsimp only [Option.map, optChainKeyAt]
    unfold vecU8
    simp only [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right ⟨cap, ptr⟩ ?_
    have ha1 : a + 72#64 + 24#64 = a + 0x60#64 := by rw [BitVec.add_assoc]; rfl
    have ha2 : a + 72#64 + 28#64 = a + 0x64#64 := by rw [BitVec.add_assoc]; rfl
    rw [ha1, ha2]
    exact Entails.refl _

private theorem prostChainGAt_recv_entails_chainAt_qrepr (A : RustAlloc) (c : ReceiverChain)
    (hseeds : ∀ mk ∈ c.messageKeys, mk.seed.length = 32)
    (hmax : c.messageKeys.length ≤ maxMessageKeys) (a : BitVec 64) :
    prostChainGAt A a (recvChainG c) ⊢
      ∃∗ cg : ChainGhost,
        ⌜CanonChain (cg, c)⌝ ∗ chainAt A (cg, c) a := by
  unfold prostChainGAt recvChainG
  dsimp only
  have hkeys :
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c.messageKeys ⊢
        ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64, ∃∗ keys : List MessageKeyGhost,
          ⌜keys.length = c.messageKeys.length ∧
            (∀ gx ∈ keys.zip c.messageKeys, True)⌝ ∗
            vecAt A 104 8 (messageKeyAt A) (a + 0x30#64) mkCap mkPtr
              (keys.zip c.messageKeys) := by
    conv_lhs => rw [show c.messageKeys = c.messageKeys.map id by simp]
    exact vecOf_map_entails_vecAt_zip_qrepr A 104 8 (fun mk b => prostMsgKeyAt A mk b)
      (messageKeyAt A) (fun _ => True) id (a + 0x30#64) c.messageKeys
      (fun mk hmk b => prostMsgKeyAt_entails_messageKeyAt_qrepr A mk (hseeds mk hmk) b)
  have hck := prostChainKey_entails_optChainKeyAt_qrepr A c.chainKey a
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono hkeys hck))) ?_
  unfold vecU8
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ckPin
  apply Entails.sepExists_elim; intro mkCap
  apply Entails.sepExists_elim; intro mkPtr
  apply Entails.sepExists_elim; intro keys
  apply Entails.sepExists_elim; intro privCap
  apply Entails.sepExists_elim; intro privPtr
  apply Entails.sepExists_elim; intro srkCap
  apply Entails.sepExists_elim; intro srkPtr
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hkeyslen, -⟩
  let cg : ChainGhost := {
    srk := ⟨srkCap, srkPtr, c.senderRatchetKey.serialize⟩
    priv := ⟨privCap, privPtr, []⟩
    mkCap := mkCap
    mkPtr := mkPtr
    keys := keys
    ck := ckPin
  }
  refine Entails.sepExists_right cg ?_
  have hcanon : CanonChain (cg, c) := ⟨rfl, rfl⟩
  refine Entails.pure_right hcanon ?_
  unfold chainAt
  refine Entails.pure_right
    ⟨deserialize_serialize_pk_qrepr c.senderRatchetKey, hmax, hkeyslen,
      serialize_pk_length_qrepr c.senderRatchetKey, rfl⟩ ?_
  dsimp only [cg, vecGhostAt]
  exact Entails.refl _

private theorem prostRecvG_entails_vecAt_chainAt_qrepr (A : RustAlloc) (s : Session (List (BitVec 8)))
    (hseeds : SeedsLen32 s.state)
    (hmax : ∀ c ∈ s.state.receiverChains, c.messageKeys.length ≤ maxMessageKeys)
    (a : BitVec 64) :
    vecOf A 104 8 (fun c p => prostChainGAt A p c) a (s.state.receiverChains.map recvChainG) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ chains : List ChainGhost,
        ⌜chains.length = s.state.receiverChains.length ∧
          (∀ gc ∈ chains.zip s.state.receiverChains, CanonChain gc)⌝ ∗
          vecAt A 104 8 (chainAt A) a cap ptr (chains.zip s.state.receiverChains) := by
  exact vecOf_map_entails_vecAt_zip_qrepr A 104 8 (fun c p => prostChainGAt A p c)
    (chainAt A) CanonChain recvChainG a s.state.receiverChains
    (fun c hc b => prostChainGAt_recv_entails_chainAt_qrepr A c (hseeds c hc) (hmax c hc) b)

private theorem vecAt_nil_prostMsgKeyAt_eq_messageKeyAt_qrepr (A : RustAlloc) (v cap ptr : BitVec 64) :
    vecAt A 104 8 (fun mk b => prostMsgKeyAt A mk b) v cap ptr [] =
      vecAt A 104 8 (messageKeyAt A) v cap ptr [] := by
  unfold vecAt vecBuf arrayAt
  rfl

private theorem prostSenderG_entails_optSenderChainAt_qrepr (A : RustAlloc) (scOpt : Option SenderChain)
    (hclamp : ∀ sc, scOpt = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (ss : BitVec 64) :
    (match scOpt.map senderChainG with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ⊢
      ∃∗ sg : Option SenderChainGhost,
        ⌜CanonSender sg scOpt⌝ ∗
          optSenderChainAt A (ss + 0x90#64) sg scOpt := by
  rcases scOpt with _ | sc
  · dsimp only [Option.map]
    refine Entails.sepExists_right none ?_
    refine Entails.pure_right trivial ?_
    unfold optSenderChainAt
    rw [show ss + 0x90#64 + 8#64 = ss + 0x98#64 by rw [BitVec.add_assoc]; rfl]
    exact Entails.refl _
  · dsimp only [Option.map]
    unfold prostChainGAt senderChainG vecU8 vecOf
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro ckCap
    apply Entails.sepExists_elim; intro ckPtr
    apply Entails.sepExists_elim; intro mkCap
    apply Entails.sepExists_elim; intro mkPtr
    apply Entails.sepExists_elim; intro privCap
    apply Entails.sepExists_elim; intro privPtr
    apply Entails.sepExists_elim; intro srkCap
    apply Entails.sepExists_elim; intro srkPtr
    let g : SenderChainGhost := {
      srk := ⟨srkCap, srkPtr, sc.ratchetKey.publicKey.serialize⟩
      priv := ⟨privCap, privPtr, sc.ratchetKey.privateKey.bytes.toList⟩
      mkCap := mkCap
      mkPtr := mkPtr
      ck := ⟨ckCap, ckPtr⟩
    }
    refine Entails.sepExists_right (some g) ?_
    have hcanon : CanonSender (some g) (some sc) := ⟨rfl, rfl⟩
    refine Entails.pure_right hcanon ?_
    unfold optSenderChainAt
    refine Entails.pure_right
      ⟨deserialize_serialize_pk_qrepr _, rfl, hclamp sc rfl, serialize_pk_length_qrepr _⟩ ?_
    dsimp only [g, vecGhostAt, optChainKeyAt]
    rw [vecAt_nil_prostMsgKeyAt_eq_messageKeyAt_qrepr,
      show ss + 0x90#64 + 72#64 + 24#64 = ss + 0x90#64 + 0x60#64 by rw [BitVec.add_assoc]; rfl,
      show ss + 0x90#64 + 72#64 + 28#64 = ss + 0x90#64 + 0x64#64 by rw [BitVec.add_assoc]; rfl]
    exact Entails.refl _

private def pendingTail_qrepr (w0 w1 spkId w2 : BitVec 32) : List (BitVec 8) :=
  unpack32 w0 ++ (unpack32 w1 ++ (unpack64 0#64 ++ (unpack32 spkId ++ unpack32 w2)))

private theorem pendingTail_length_qrepr (w0 w1 spkId w2 : BitVec 32) :
    (pendingTail_qrepr w0 w1 spkId w2).length = 24 := rfl

private theorem pendingTail_pointsToBytes_qrepr (ss : BitVec 64) (w0 w1 spkId w2 : BitVec 32) :
    ((ss + 0x110#64) ↦₃₂ w0) ∗ ((ss + 0x114#64) ↦₃₂ w1) ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
      ((ss + 0x120#64) ↦₃₂ spkId) ∗ ((ss + 0x124#64) ↦₃₂ w2) =
      ((ss + 0xf8#64 + 24#64) ↦ₛ pendingTail_qrepr w0 w1 spkId w2) := by
  have ha0 : ss + 0xf8#64 + 24#64 = ss + 0x110#64 := by rw [BitVec.add_assoc]; rfl
  have ha1 : ss + 0x110#64 + 4#64 = ss + 0x114#64 := by rw [BitVec.add_assoc]; rfl
  have ha2 : ss + 0x114#64 + 4#64 = ss + 0x118#64 := by rw [BitVec.add_assoc]; rfl
  have ha3 : ss + 0x118#64 + 8#64 = ss + 0x120#64 := by rw [BitVec.add_assoc]; rfl
  have ha4 : ss + 0x120#64 + 4#64 = ss + 0x124#64 := by rw [BitVec.add_assoc]; rfl
  unfold pendingTail_qrepr
  rw [ha0, pointsToBytes_append, unpack32_length,
    ha1, pointsToBytes_append, unpack32_length,
    ha2, pointsToBytes_append, unpack64_length,
    ha3, pointsToBytes_append, unpack32_length, ha4]
  simp only [← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]

private theorem prostPending_entails_optTailVecAt_qrepr (A : RustAlloc) (s : Session (List (BitVec 8)))
    (hwf : s.Wf)
    (hp : ∀ p, s.pendingPreKey = some p → p.timestamp = 0)
    (ss : BitVec 64) (pid : Option (BitVec 32)) (spkId : BitVec 32)
    (hpid : ∀ p, s.pendingPreKey = some p → pid = p.preKeyId ∧ spkId = p.signedPreKeyId) :
    (match s.pendingPreKey.map (fun p => p.baseKey.serialize) with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ spkId) ∗ memRegion (ss + 0x124#64) 4)) ⊢
      ∃∗ pg : Option TailVecGhost,
        ⌜CanonPending pg s.pendingPreKey ∧
          PendingRel pg s.pendingPreKey ∧
          pg.isSome = s.state.pendingPreKey⌝ ∗
          optTailVecAt A 48 (ss + 0xf8#64) pg := by
  unfold Session.Wf at hwf
  rcases hpend : s.pendingPreKey with _ | p
  · dsimp only [Option.map]
    refine Entails.sepExists_right none ?_
    have hsome : (none : Option TailVecGhost).isSome = s.state.pendingPreKey := by
      rw [hwf, hpend]; rfl
    refine Entails.pure_right ⟨trivial, trivial, hsome⟩ ?_
    unfold optTailVecAt
    rw [show ss + 0xf8#64 + 8#64 = ss + 0x100#64 by rw [BitVec.add_assoc]; rfl]
    exact Entails.refl _
  · dsimp only [Option.map]
    have hts := hp p hpend
    obtain ⟨hpid', hspk'⟩ := hpid p hpend
    have hsome : (some (⟨⟨0, 0, []⟩, []⟩ : TailVecGhost)).isSome = s.state.pendingPreKey := by
      rw [hwf, hpend]; rfl
    subst hspk'
    rcases hpre : p.preKeyId with _ | i <;> rw [hpre] at hpid' <;> subst hpid'
    · unfold pidAt vecU8
      rw [memRegion_four (ss + 0x114#64), memRegion_four (ss + 0x124#64)]
      simp only [sepExists_sepConj_right, sepExists_sepConj_left]
      refine Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w1 =>
        Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
      let g : TailVecGhost := {
        vec := ⟨cap, ptr, p.baseKey.serialize⟩
        tail := pendingTail_qrepr 0#32 w1 p.signedPreKeyId w2
      }
      refine Entails.sepExists_right (some g) ?_
      have hcanon : CanonPending (some g) (some p) := rfl
      have hrel : PendingRel (some g) (some p) := by
        refine ⟨deserialize_serialize_pk_qrepr p.baseKey, ?_, ?_, ?_, serialize_pk_length_qrepr p.baseKey⟩
        · rw [hpre]; rfl
        · rw [hts]; rfl
        · simp only [g, pendingTail_qrepr, leBytes, unpack32, unpack64, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl
      refine Entails.pure_right ⟨hcanon, hrel, hsome⟩ ?_
      unfold optTailVecAt
      refine Entails.pure_right (pendingTail_length_qrepr 0#32 w1 p.signedPreKeyId w2) ?_
      dsimp only [g, vecGhostAt]
      rw [← pendingTail_pointsToBytes_qrepr ss 0#32 w1 p.signedPreKeyId w2]
      exact Entails.refl _
    · unfold pidAt vecU8
      rw [memRegion_four (ss + 0x124#64)]
      simp only [sepExists_sepConj_right, sepExists_sepConj_left]
      refine Entails.sepExists_elim fun w2 =>
        Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
      let g : TailVecGhost := {
        vec := ⟨cap, ptr, p.baseKey.serialize⟩
        tail := pendingTail_qrepr 1#32 i p.signedPreKeyId w2
      }
      refine Entails.sepExists_right (some g) ?_
      have hcanon : CanonPending (some g) (some p) := rfl
      have hrel : PendingRel (some g) (some p) := by
        refine ⟨deserialize_serialize_pk_qrepr p.baseKey, ?_, ?_, ?_, serialize_pk_length_qrepr p.baseKey⟩
        · rw [hpre]; exact ⟨rfl, by simp only [g, pendingTail_qrepr, leBytes, unpack32, unpack64, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl⟩
        · rw [hts]; rfl
        · simp only [g, pendingTail_qrepr, leBytes, unpack32, unpack64, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl
      refine Entails.pure_right ⟨hcanon, hrel, hsome⟩ ?_
      unfold optTailVecAt
      refine Entails.pure_right (pendingTail_length_qrepr 1#32 i p.signedPreKeyId w2) ?_
      dsimp only [g, vecGhostAt]
      rw [← pendingTail_pointsToBytes_qrepr ss 1#32 i p.signedPreKeyId w2]
      exact Entails.refl _

private theorem kyberAt_split_qrepr (A : RustAlloc) (ss : BitVec 64)
    (kyber : Option (BitVec 32 × List (BitVec 8))) (R : SepProp) :
    kyberAt A ss kyber R =
      (match kyber with
       | none => ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24
       | some (i, ct) => vecU8 A (ss + 0x128#64) ct ∗ ((ss + 0x140#64) ↦₃₂ i) ∗
           memRegion (ss + 0x144#64) 4) ∗ R := by
  rcases kyber with _ | ⟨i, ct⟩ <;> simp only [kyberAt, sepConj_assoc]

private def kyberTail_qrepr (i w : BitVec 32) : List (BitVec 8) := unpack32 i ++ unpack32 w

private theorem kyberTail_pointsToBytes_qrepr (ss : BitVec 64) (i w : BitVec 32) :
    ((ss + 0x140#64) ↦₃₂ i) ∗ ((ss + 0x144#64) ↦₃₂ w) =
      ((ss + 0x128#64 + 24#64) ↦ₛ kyberTail_qrepr i w) := by
  have ha0 : ss + 0x128#64 + 24#64 = ss + 0x140#64 := by rw [BitVec.add_assoc]; rfl
  have ha1 : ss + 0x140#64 + 4#64 = ss + 0x144#64 := by rw [BitVec.add_assoc]; rfl
  unfold kyberTail_qrepr
  rw [ha0, pointsToBytes_append, unpack32_length, ha1]
  simp only [← pointsTo32_eq_pointsToBytes]

private theorem prostKyber_entails_optTailVecAt_qrepr (A : RustAlloc) (o : Option PendingKyberPreKey)
    (ss : BitVec 64) :
    (match o.map (fun k => (k.preKeyId, k.ciphertext)) with
     | none => ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24
     | some (i, ct) => vecU8 A (ss + 0x128#64) ct ∗ ((ss + 0x140#64) ↦₃₂ i) ∗
         memRegion (ss + 0x144#64) 4) ⊢
      ∃∗ kg : Option TailVecGhost, ⌜KyberRel kg o⌝ ∗ optTailVecAt A 32 (ss + 0x128#64) kg := by
  rcases ho : o with _ | k
  · dsimp only [Option.map]
    refine Entails.sepExists_right none ?_
    refine Entails.pure_right trivial ?_
    unfold optTailVecAt
    rw [show ss + 0x128#64 + 8#64 = ss + 0x130#64 by rw [BitVec.add_assoc]; rfl]
    exact Entails.refl _
  · dsimp only [Option.map]
    unfold vecU8
    rw [memRegion_four (ss + 0x144#64)]
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    refine Entails.sepExists_elim fun w =>
      Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
    let g : TailVecGhost := {
      vec := ⟨cap, ptr, k.ciphertext⟩
      tail := kyberTail_qrepr k.preKeyId w
    }
    refine Entails.sepExists_right (some g) ?_
    have hrel : KyberRel (some g) (some k) := by
      refine ⟨rfl, ?_⟩
      dsimp only [g, kyberTail_qrepr]
      simp only [g, pendingTail_qrepr, kyberTail_qrepr, leBytes, unpack32, unpack64, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl
    refine Entails.pure_right hrel ?_
    unfold optTailVecAt
    refine Entails.pure_right (rfl : (kyberTail_qrepr k.preKeyId w).length = 8) ?_
    dsimp only [g, vecGhostAt]
    rw [← kyberTail_pointsToBytes_qrepr ss k.preKeyId w]
    exact Entails.refl _

/-- The decoded `Q`-scope `SessionStructure` (`prostSSGQAt A a (ssgqOf s)`) of a
`DeserializeScopeP_Q Q` session represents `sessionStateReprAt` with a `CanonSession` ghost. -/
theorem prostSSGQ_reprA {Q : List (BitVec 8) → Prop} (A : RustAlloc)
    (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP_Q Q r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) (a : BitVec 64) :
    prostSSGQAt A a (ssgqOf s) ⊢
      ∃∗ G : SessionGhost, ⌜CanonSession G s⌝ ∗ sessionStateReprAt A a G s := by
  obtain ⟨⟨hr_in, _hr_q, hr_repr⟩, s', hs', hscope⟩ := hr
  have hss' : s = s' := Option.some.inj (hs.symm.trans hs')
  subst hss'
  obtain ⟨hseeds, -, -⟩ := hr_in s hs
  obtain ⟨hmax_mk, hclamp, hwf, -⟩ := hr_repr s hs
  obtain ⟨-, hpend_fields, -⟩ := hscope
  unfold prostSSGQAt ssgqOf ssgOf
  dsimp only
  rw [kyberAt_split_qrepr]
  have hrecv := prostRecvG_entails_vecAt_chainAt_qrepr A s hseeds hmax_mk (a + 0x48#64)
  have hsender := prostSenderG_entails_optSenderChainAt_qrepr A s.state.senderChain hclamp a
  have hpending := prostPending_entails_optTailVecAt_qrepr A s hwf hpend_fields a
    (s.pendingPreKey.bind (·.preKeyId))
    ((s.pendingPreKey.map (·.signedPreKeyId)).getD 0#32)
    (fun p hp => by rw [hp]; exact ⟨rfl, rfl⟩)
  have hky := prostKyber_entails_optTailVecAt_qrepr A s.pendingKyberPreKey a
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left hrecv)))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  refine Entails.sepExists_elim fun chainsCap => Entails.sepExists_elim fun chainsPtr =>
    Entails.sepExists_elim fun chains => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hchains_len, hchains_canon⟩
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hsender))))))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro sg
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hsender_canon
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hpending)))))))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro pg
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hpending_canon, hpending_rel, hpending_some⟩
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hky))))))))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro kg
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hkyber_rel
  unfold vecU8
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  refine Entails.sepExists_elim fun pqCap => Entails.sepExists_elim fun pqPtr =>
    Entails.sepExists_elim fun aliceCap => Entails.sepExists_elim fun alicePtr =>
    Entails.sepExists_elim fun rootCap => Entails.sepExists_elim fun rootPtr =>
    Entails.sepExists_elim fun rikCap => Entails.sepExists_elim fun rikPtr =>
    Entails.sepExists_elim fun likCap => Entails.sepExists_elim fun likPtr => ?_
  let G : SessionGhost := {
    localIk := ⟨likCap, likPtr, s.state.localIdentity.serialize⟩
    remoteIk := ⟨rikCap, rikPtr, (s.state.remoteIdentity.map IdentityKey.serialize).getD []⟩
    root := ⟨rootCap, rootPtr⟩, chainsCap := chainsCap, chainsPtr := chainsPtr, chains := chains
    alice := ⟨aliceCap, alicePtr, s.aliceBaseKey⟩, pq := ⟨pqCap, pqPtr⟩
    sender := sg, pending := pg, kyber := kg
    regIds := unpack32 s.remoteRegistrationId ++ unpack32 s.localRegistrationId }
  refine Entails.sepExists_right G ?_
  have hcanon : CanonSession G s :=
    ⟨rfl, rfl, hsender_canon, hchains_len, hchains_canon, hpending_canon⟩
  refine Entails.pure_right hcanon ?_
  unfold sessionStateReprAt
  have halice_eq : G.alice.bytes = s.aliceBaseKey := rfl
  have hreg1 : G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat := by
    simp only [G, leBytes, unpack32, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl
  have hreg2 : (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat := by
    simp only [G, leBytes, unpack32, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl
  refine Entails.pure_right ⟨hpending_rel, hkyber_rel, halice_eq, hreg1, hreg2⟩ ?_
  unfold sessionStateAt
  have hrem_deser :
      match s.state.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey := by
    dsimp only [G]
    rcases s.state.remoteIdentity with _ | ik
    · rfl
    · exact deserialize_serialize_pk_qrepr ik.publicKey
  have hrem_len : s.state.remoteIdentity.isSome → G.remoteIk.bytes.length = 33 := by
    dsimp only [G]
    rcases s.state.remoteIdentity with _ | ik <;> simp [serialize_ik_length_qrepr]
  have hst_pure :
      PublicKey.deserialize G.localIk.bytes = .ok s.state.localIdentity.publicKey ∧
      (match s.state.remoteIdentity with
       | none => G.remoteIk.bytes = []
       | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
      G.chains.length = s.state.receiverChains.length ∧
      G.pending.isSome = s.state.pendingPreKey ∧
      G.regIds.length = 8 ∧
      G.localIk.bytes.length = 33 ∧
      (s.state.remoteIdentity.isSome → G.remoteIk.bytes.length = 33) :=
    ⟨deserialize_serialize_pk_qrepr s.state.localIdentity.publicKey,
      hrem_deser, hchains_len, hpending_some, rfl,
      serialize_ik_length_qrepr s.state.localIdentity, hrem_len⟩
  refine Entails.pure_right hst_pure ?_
  dsimp only [G, vecGhostAt]
  have ha150 : a + 0x150#64 + 4#64 = a + 0x154#64 := by rw [BitVec.add_assoc]; rfl
  rw [pointsToBytes_append, unpack32_length, ha150,
    ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  exact Entails.refl _

theorem prostSSGQ_repr {Q : List (BitVec 8) → Prop}
    (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP_Q Q r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) (a : BitVec 64) :
    prostSSGQAt A0 a (ssgqOf s) ⊢
      ∃∗ G : SessionGhost, ⌜CanonSession G s⌝ ∗ sessionStateReprAt A0 a G s :=
  prostSSGQ_reprA A0 r hr s hs a

/-! ## `deserOutRecordQA` to `CanonRecord` and `BinCanonSession` -/

private theorem vecAt_prev_zero_eq_qrepr (A : RustAlloc) (out : BitVec 64) :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) out 0#64 8#64 [] =
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) := by
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧
      (8#64 : BitVec 64) ≠ 0#64) := by decide
  unfold vecAt vecHeader vecBuf
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ite_true, sepConj_emp,
    SeedLengthFacts.pure_true_sepConj hpure]

/-- Raw `Ok(record)` output (`deserOutRecordQA`) represents `r` with a `CanonRecord` ghost. -/
theorem deserReprQA_ok {Q : List (BitVec 8) → Prop} (A : RustAlloc)
    (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP_Q Q r) (out : BitVec 64) :
    deserOutRecordQA A out r ⊢
      ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A out g r := by
  obtain ⟨s, hs, _⟩ := hr.2
  have hdef :
      deserOutRecordQA A out r =
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          prostSSGQAt A (out + 0x18#64) (ssgqOf s) := by
    unfold deserOutRecordQA
    rw [ssgqAfter_recFieldsQ r hr s hs]
    ac_rfl
  rw [hdef]
  refine Entails.trans (sepConj_mono_right (prostSSGQ_reprA A r hr s hs (out + 0x18#64))) ?_
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun G => ?_
  have h1 :
      (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
        (⌜CanonSession G s⌝ ∗ sessionStateReprAt A (out + 0x18#64) G s)) =
      (⌜CanonSession G s⌝ ∗
        (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          sessionStateReprAt A (out + 0x18#64) G s)) := by
    ac_rfl
  rw [h1]
  refine Entails.pure_left fun hcanon => ?_
  refine Entails.sepExists_right ⟨0#64, 8#64, some G⟩ ?_
  refine Entails.pure_right ?_ ?_
  · unfold CanonRecord CanonCur
    rw [hs]
    exact hcanon
  · unfold sessionRecordAt
    rw [hs]
    dsimp only
    rw [vecAt_prev_zero_eq_qrepr A]
    exact Entails.refl _

theorem deserReprQ_ok {Q : List (BitVec 8) → Prop}
    (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP_Q Q r) (out : BitVec 64) :
    deserOutRecordQ out r ⊢
      ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A0 out g r :=
  deserReprQA_ok A0 r hr out

private theorem mem_zip_of_mem_left_qrepr :
    ∀ {α β : Type} {xs : List α} {ys : List β} {x : α},
      xs.length = ys.length → x ∈ xs → ∃ y, (x, y) ∈ xs.zip ys
  | _, _, [], [], _, _, hx => by simp at hx
  | _, _, x' :: xs, y' :: ys, x, hlen, hx => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨y', List.mem_cons_self ..⟩
    · obtain ⟨y, hy⟩ := mem_zip_of_mem_left_qrepr hlen hx
      exact ⟨y, List.mem_cons_of_mem _ hy⟩

/-- Transport `BinCanonSession` from an existing ghost `G0` to any `CanonSession G s`. -/
theorem binCanonSession_of_canonSessionQ {G0 G : SessionGhost} {s : Session (List (BitVec 8))}
    (h0 : BinCanonSession G0 s) (hG : CanonSession G s) :
    BinCanonSession G s := by
  rcases h0 with ⟨_, hwf, _, _, _, hrc_len, hrc_mk, _, halice, hkyber, hpq, henc⟩
  rcases hG with ⟨hlocal, hrem, hsender, hlen_eq, hzip, hpend⟩
  refine ⟨⟨hlocal, hrem, hsender, hlen_eq, hzip, hpend⟩,
    hwf, hlocal, ?_, ?_, hrc_len, hrc_mk, ?_, halice, hkyber, hpq, henc⟩
  · cases hri : s.state.remoteIdentity <;> simpa [hri] using hrem
  · revert hsender
    unfold CanonSender
    cases G.sender <;> cases s.state.senderChain <;> intro hsender
    · exact True.intro
    · exact hsender
    · exact hsender
    · exact hsender.1
  · intro cg hcg
    obtain ⟨rc, hmem⟩ := mem_zip_of_mem_left_qrepr hlen_eq hcg
    have hcc := hzip (cg, rc) hmem
    have hser_len : rc.senderRatchetKey.serialize.length = 33 :=
      serialize_pk_length_qrepr rc.senderRatchetKey
    exact ⟨hcc.1.trans (by rfl) ▸ hser_len, hcc.2⟩

/-- `deserOutRecordQA` entails `sessionRecordAt` with a `BinCanonSession` ghost. -/
theorem deserOutRecordQA_entails_binCanonSession {Q : List (BitVec 8) → Prop} (A : RustAlloc)
    {G0 : SessionGhost} (s : Session (List (BitVec 8)))
    (h0 : BinCanonSession G0 s) (hr : DeserializeScopeP_Q Q ⟨some s⟩) (out : BitVec 64) :
    deserOutRecordQA A out ⟨some s⟩ ⊢
      ∃∗ G : SessionGhost, ⌜BinCanonSession G s⌝ ∗
        sessionRecordAt A out ⟨0#64, 8#64, some G⟩ ⟨some s⟩ := by
  have hAfter := ssgqAfter_recFieldsQ ⟨some s⟩ hr s rfl
  have hRepr := prostSSGQ_reprA A ⟨some s⟩ hr s rfl (out + 0x18#64)
  have hdef :
      deserOutRecordQA A out ⟨some s⟩ =
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          prostSSGQAt A (out + 0x18#64) (ssgqOf s) := by
    unfold deserOutRecordQA
    rw [hAfter]
    ac_rfl
  rw [hdef]
  refine Entails.trans (sepConj_mono_right hRepr) ?_
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun G => ?_
  have h1 :
      (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
        (⌜CanonSession G s⌝ ∗ sessionStateReprAt A (out + 0x18#64) G s)) =
      (⌜CanonSession G s⌝ ∗
        (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          sessionStateReprAt A (out + 0x18#64) G s)) := by
    ac_rfl
  rw [h1]
  refine Entails.pure_left fun hcanon => ?_
  refine Entails.sepExists_right G ?_
  refine Entails.pure_right (binCanonSession_of_canonSessionQ h0 hcanon) ?_
  unfold sessionRecordAt
  dsimp only
  rw [vecAt_prev_zero_eq_qrepr A]
  exact Entails.refl _

theorem deserOutRecordQ_entails_binCanonSession {Q : List (BitVec 8) → Prop}
    {G0 : SessionGhost} (s : Session (List (BitVec 8)))
    (h0 : BinCanonSession G0 s) (hr : DeserializeScopeP_Q Q ⟨some s⟩) (out : BitVec 64) :
    deserOutRecordQ out ⟨some s⟩ ⊢
      ∃∗ G : SessionGhost, ⌜BinCanonSession G s⌝ ∗
        sessionRecordAt A0 out ⟨0#64, 8#64, some G⟩ ⟨some s⟩ :=
  deserOutRecordQA_entails_binCanonSession A0 s h0 hr out

end Symbolic.Swarm.TRREF.B3DeserQ
