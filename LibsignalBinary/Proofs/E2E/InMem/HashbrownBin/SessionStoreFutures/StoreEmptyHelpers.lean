/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.Common
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon

/-!
# `InMemSessionStore::store_session::{closure#0}` (`0x08ee4`) on an Empty Table

Proves `storeSessionEmpty_ok'` against `storeSessionEmptySpec A`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.HashbrownBin
open LoadSingle

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CanonSession
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem emptyTableAt_eq (base mp k0 k1 : BitVec 64) :
    emptyTableAt base mp k0 k1 =
      (mp ↦₆₄ (base + BitVec.ofNat 64 emptyCtrlGroupOff)) ∗
      ((mp + 8#64) ↦₆₄ 0#64) ∗
      ((mp + 16#64) ↦₆₄ 0#64) ∗
      ((mp + 24#64) ↦₆₄ 0#64) ∗
      ((mp + 32#64) ↦₆₄ k0) ∗
      ((mp + 40#64) ↦₆₄ k1) := by
  have hadd : mp + 32#64 + 8#64 = mp + 40#64 := by bv_omega
  dsimp only [emptyTableAt]
  rw [hadd]

theorem table4EmptyAt_eq (A : RustAlloc) (stride : Nat) (mp k0 k1 : BitVec 64) :
    table4EmptyAt A stride mp k0 k1 =
      ∃∗ ctrl : BitVec 64,
        ⌜ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧
          4 * stride ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64 ∧
          (([] : List Nat).length = 4 → 3#64 = 0#64) ∧
          CtrlMirrorInv 3#64 emptyCtrl4 ∧
          FullBucketsInv 3#64 emptyCtrl4 []⌝ ∗
        (mp ↦₆₄ ctrl) ∗
        ((mp + 8#64) ↦₆₄ 3#64) ∗
        ((mp + 16#64) ↦₆₄ 3#64) ∗
        ((mp + 24#64) ↦₆₄ 0#64) ∗
        ((mp + 32#64) ↦₆₄ k0) ∗
        ((mp + 40#64) ↦₆₄ k1) ∗
        A.live (ctrl - BitVec.ofNat 64 (4 * stride)) (tableAllocSize 4 stride) 8 ∗
        (ctrl ↦ₛ emptyCtrl4) ∗
        arrayAt
          (fun i a => if i ∈ ([] : List Nat) then memRegion a stride else memRegion a stride) stride
          (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse := by
  have hadd : mp + 32#64 + 8#64 = mp + 40#64 := by bv_omega
  dsimp only [table4EmptyAt, table4At]
  rw [hadd]
  rfl

theorem arrayAt_table4Empty_split_400 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    arrayAt
      (fun i a => if i ∈ ([] : List Nat) then memRegion a 400 else memRegion a 400) 400
      (ctrl - BitVec.ofNat 64 (4 * 400)) (List.range 4).reverse =
    memRegion (bucketAddr ctrl 400 k) 400 ∗ singleBucketRestAt 400 ctrl k := by
  have hfun :
      (fun (i : Nat) (a : BitVec 64) => if i ∈ ([] : List Nat) then memRegion a 400 else memRegion a 400) =
      (fun i a => if i ∈ [k] then memRegion a 400 else memRegion a 400) := by
    funext i a; simp
  rw [hfun]
  exact arrayAt_single_split_400 ctrl k hk (fun a => memRegion a 400)

theorem loadGroupAt_emptyCtrl4 (k : Nat) (hk : k < 4) :
    loadGroupAt emptyCtrl4 k = 0xffffffffffffffff#64 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    decide +kernel

def emptyCtrl4RestAt (ctrl : BitVec 64) (k : Nat) : SepProp :=
  (ctrl ↦ₛ emptyCtrl4.take k) ∗
  ((ctrl + BitVec.ofNat 64 (k + 1)) ↦ₛ (emptyCtrl4.drop (k + 1)).take 7) ∗
  ((ctrl + BitVec.ofNat 64 (k + 9)) ↦ₛ emptyCtrl4.drop (k + 9))

theorem emptyCtrl4_split_k_and_k8 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    (ctrl ↦ₛ emptyCtrl4) =
      ((ctrl + BitVec.ofNat 64 k) ↦₈ 0xff#8) ∗
      ((ctrl + BitVec.ofNat 64 k + 8#64) ↦₈ 0xff#8) ∗
      emptyCtrl4RestAt ctrl k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [emptyCtrl4RestAt, emptyCtrl4, mkCtrl4, emptyTag, List.take, List.drop,
      pointsToBytes_cons, pointsToBytes_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    simp only [
      show ctrl + 0#64 = ctrl by bv_omega,
      show ctrl + 0#64 + 8#64 = ctrl + 8#64 by bv_omega,
      show ctrl + 1#64 + 0#64 = ctrl + 1#64 by bv_omega,
      show ctrl + 1#64 + 1#64 = ctrl + 2#64 by bv_omega,
      show ctrl + 1#64 + 2#64 = ctrl + 3#64 by bv_omega,
      show ctrl + 1#64 + 3#64 = ctrl + 4#64 by bv_omega,
      show ctrl + 1#64 + 4#64 = ctrl + 5#64 by bv_omega,
      show ctrl + 1#64 + 5#64 = ctrl + 6#64 by bv_omega,
      show ctrl + 1#64 + 6#64 = ctrl + 7#64 by bv_omega,
      show ctrl + 1#64 + 7#64 = ctrl + 8#64 by bv_omega,
      show ctrl + 1#64 + 8#64 = ctrl + 9#64 by bv_omega,
      show ctrl + 2#64 + 0#64 = ctrl + 2#64 by bv_omega,
      show ctrl + 2#64 + 1#64 = ctrl + 3#64 by bv_omega,
      show ctrl + 2#64 + 2#64 = ctrl + 4#64 by bv_omega,
      show ctrl + 2#64 + 3#64 = ctrl + 5#64 by bv_omega,
      show ctrl + 2#64 + 4#64 = ctrl + 6#64 by bv_omega,
      show ctrl + 2#64 + 5#64 = ctrl + 7#64 by bv_omega,
      show ctrl + 2#64 + 6#64 = ctrl + 8#64 by bv_omega,
      show ctrl + 2#64 + 7#64 = ctrl + 9#64 by bv_omega,
      show ctrl + 2#64 + 8#64 = ctrl + 10#64 by bv_omega,
      show ctrl + 3#64 + 0#64 = ctrl + 3#64 by bv_omega,
      show ctrl + 3#64 + 1#64 = ctrl + 4#64 by bv_omega,
      show ctrl + 3#64 + 2#64 = ctrl + 5#64 by bv_omega,
      show ctrl + 3#64 + 3#64 = ctrl + 6#64 by bv_omega,
      show ctrl + 3#64 + 4#64 = ctrl + 7#64 by bv_omega,
      show ctrl + 3#64 + 5#64 = ctrl + 8#64 by bv_omega,
      show ctrl + 3#64 + 6#64 = ctrl + 9#64 by bv_omega,
      show ctrl + 3#64 + 8#64 = ctrl + 11#64 by bv_omega,
      show ctrl + 4#64 + 0#64 = ctrl + 4#64 by bv_omega,
      show ctrl + 4#64 + 1#64 = ctrl + 5#64 by bv_omega,
      show ctrl + 4#64 + 2#64 = ctrl + 6#64 by bv_omega,
      show ctrl + 4#64 + 3#64 = ctrl + 7#64 by bv_omega,
      show ctrl + 4#64 + 4#64 = ctrl + 8#64 by bv_omega,
      show ctrl + 4#64 + 5#64 = ctrl + 9#64 by bv_omega,
      show ctrl + 4#64 + 6#64 = ctrl + 10#64 by bv_omega,
      show ctrl + 5#64 + 1#64 = ctrl + 6#64 by bv_omega,
      show ctrl + 6#64 + 1#64 = ctrl + 7#64 by bv_omega,
      show ctrl + 7#64 + 1#64 = ctrl + 8#64 by bv_omega,
      show ctrl + 8#64 + 1#64 = ctrl + 9#64 by bv_omega,
      show ctrl + 9#64 + 0#64 = ctrl + 9#64 by bv_omega,
      show ctrl + 9#64 + 1#64 = ctrl + 10#64 by bv_omega,
      show ctrl + 9#64 + 2#64 = ctrl + 11#64 by bv_omega,
      show ctrl + 10#64 + 0#64 = ctrl + 10#64 by bv_omega,
      show ctrl + 10#64 + 1#64 = ctrl + 11#64 by bv_omega,
      show ctrl + 11#64 + 0#64 = ctrl + 11#64 by bv_omega]
    ac_rfl

theorem singleCtrl4_of_write_k_and_k8 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) (tag : BitVec 8) :
    (((ctrl + BitVec.ofNat 64 k) ↦₈ tag) ∗
      ((ctrl + BitVec.ofNat 64 k + 8#64) ↦₈ tag) ∗
      emptyCtrl4RestAt ctrl k) =
    (ctrl ↦ₛ singleCtrl4 k tag) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [emptyCtrl4RestAt, emptyCtrl4, singleCtrl4, mkCtrl4, emptyTag, List.take, List.drop,
      pointsToBytes_cons, pointsToBytes_nil, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte,
      BitVec.ofNat_eq_ofNat]
    simp only [
      show ctrl + 0#64 = ctrl by bv_omega,
      show ctrl + 0#64 + 8#64 = ctrl + 8#64 by bv_omega,
      show ctrl + 1#64 + 0#64 = ctrl + 1#64 by bv_omega,
      show ctrl + 1#64 + 1#64 = ctrl + 2#64 by bv_omega,
      show ctrl + 1#64 + 2#64 = ctrl + 3#64 by bv_omega,
      show ctrl + 1#64 + 3#64 = ctrl + 4#64 by bv_omega,
      show ctrl + 1#64 + 4#64 = ctrl + 5#64 by bv_omega,
      show ctrl + 1#64 + 5#64 = ctrl + 6#64 by bv_omega,
      show ctrl + 1#64 + 6#64 = ctrl + 7#64 by bv_omega,
      show ctrl + 1#64 + 7#64 = ctrl + 8#64 by bv_omega,
      show ctrl + 1#64 + 8#64 = ctrl + 9#64 by bv_omega,
      show ctrl + 2#64 + 0#64 = ctrl + 2#64 by bv_omega,
      show ctrl + 2#64 + 1#64 = ctrl + 3#64 by bv_omega,
      show ctrl + 2#64 + 2#64 = ctrl + 4#64 by bv_omega,
      show ctrl + 2#64 + 3#64 = ctrl + 5#64 by bv_omega,
      show ctrl + 2#64 + 4#64 = ctrl + 6#64 by bv_omega,
      show ctrl + 2#64 + 5#64 = ctrl + 7#64 by bv_omega,
      show ctrl + 2#64 + 6#64 = ctrl + 8#64 by bv_omega,
      show ctrl + 2#64 + 7#64 = ctrl + 9#64 by bv_omega,
      show ctrl + 2#64 + 8#64 = ctrl + 10#64 by bv_omega,
      show ctrl + 3#64 + 0#64 = ctrl + 3#64 by bv_omega,
      show ctrl + 3#64 + 1#64 = ctrl + 4#64 by bv_omega,
      show ctrl + 3#64 + 2#64 = ctrl + 5#64 by bv_omega,
      show ctrl + 3#64 + 3#64 = ctrl + 6#64 by bv_omega,
      show ctrl + 3#64 + 4#64 = ctrl + 7#64 by bv_omega,
      show ctrl + 3#64 + 5#64 = ctrl + 8#64 by bv_omega,
      show ctrl + 3#64 + 6#64 = ctrl + 9#64 by bv_omega,
      show ctrl + 3#64 + 8#64 = ctrl + 11#64 by bv_omega,
      show ctrl + 4#64 + 0#64 = ctrl + 4#64 by bv_omega,
      show ctrl + 4#64 + 1#64 = ctrl + 5#64 by bv_omega,
      show ctrl + 4#64 + 2#64 = ctrl + 6#64 by bv_omega,
      show ctrl + 4#64 + 3#64 = ctrl + 7#64 by bv_omega,
      show ctrl + 4#64 + 4#64 = ctrl + 8#64 by bv_omega,
      show ctrl + 4#64 + 5#64 = ctrl + 9#64 by bv_omega,
      show ctrl + 4#64 + 6#64 = ctrl + 10#64 by bv_omega,
      show ctrl + 5#64 + 1#64 = ctrl + 6#64 by bv_omega,
      show ctrl + 6#64 + 1#64 = ctrl + 7#64 by bv_omega,
      show ctrl + 7#64 + 1#64 = ctrl + 8#64 by bv_omega,
      show ctrl + 8#64 + 1#64 = ctrl + 9#64 by bv_omega,
      show ctrl + 9#64 + 0#64 = ctrl + 9#64 by bv_omega,
      show ctrl + 9#64 + 1#64 = ctrl + 10#64 by bv_omega,
      show ctrl + 9#64 + 2#64 = ctrl + 11#64 by bv_omega,
      show ctrl + 10#64 + 0#64 = ctrl + 10#64 by bv_omega,
      show ctrl + 10#64 + 1#64 = ctrl + 11#64 by bv_omega,
      show ctrl + 11#64 + 0#64 = ctrl + 11#64 by bv_omega]
    ac_rfl

theorem sub8_and3_eq (k : Nat) (hk : k < 4) :
    (BitVec.ofNat 64 k - 8#64) &&& 3#64 = BitVec.ofNat 64 k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem h2Tag_eq_truncate8_ushiftRight57 (h : BitVec 64) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (h >>> 57))) = h2Tag h := by
  unfold h2Tag
  bv_slice

theorem zeroExtend8_ushr57_eq_h2Tag (h : BitVec 64) :
    BitVec.zeroExtend 8 (h >>> 57) = h2Tag h := by
  unfold h2Tag
  bv_slice

theorem pack64_truncate8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).truncate 8 = b0 := by
  dsimp only [pack64]
  bv_slice

theorem addrClone_to_4words (A : RustAlloc) (sp : BitVec 64) (g : AddrGhost)
    (hlen36 : g.name.bytes.length = 36) :
    protocolAddressAt A g (sp - 1264#64) ⊢
      ∃∗ w_dev : BitVec 64,
        ⌜w_dev.truncate 8 = g.device ∧
          g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        ((sp - 1264#64) ↦₆₄ g.name.cap) ∗
        ((sp - 1256#64) ↦₆₄ g.name.ptr) ∗
        ((sp - 1248#64) ↦₆₄ 36#64) ∗
        ((sp - 1240#64) ↦₆₄ w_dev) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        A.live g.name.ptr g.name.cap.toNat 1 ∗
        memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
          (g.name.cap.toNat - g.name.bytes.length) := by
  rw [protocolAddressAt_eq_of_len36 A g (sp - 1264#64) hlen36]
  unfold addrRestAt
  have e8 : sp - 1264#64 + 8#64 = sp - 1256#64 := by bv_omega
  have e16 : sp - 1264#64 + 16#64 = sp - 1248#64 := by bv_omega
  have e24 : sp - 1264#64 + 24#64 = sp - 1240#64 := by bv_omega
  have e25 : sp - 1264#64 + 25#64 = sp - 1239#64 := by bv_omega
  rw [e8, e16, e24, e25]
  rw [memRegion_eq_exists_bytes (sp - 1239#64) 7 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro pad7
  have h1 :
      (((sp - 1256#64) ↦₆₄ g.name.ptr) ∗
        ((sp - 1248#64) ↦₆₄ 36#64) ∗
        ((sp - 1240#64) ↦₈ g.device) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          ((sp - 1264#64) ↦₆₄ g.name.cap) ∗
          A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length) ∗
          (⌜pad7.length = 7⌝ ∗ ((sp - 1239#64) ↦ₛ pad7)))) =
      (⌜pad7.length = 7⌝ ∗
        ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        ((sp - 1264#64) ↦₆₄ g.name.cap) ∗
        ((sp - 1256#64) ↦₆₄ g.name.ptr) ∗
        ((sp - 1248#64) ↦₆₄ 36#64) ∗
        (((sp - 1240#64) ↦₈ g.device) ∗ ((sp - 1239#64) ↦ₛ pad7)) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        A.live g.name.ptr g.name.cap.toNat 1 ∗
        memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
          (g.name.cap.toNat - g.name.bytes.length)) := by ac_rfl
  rw [h1]
  apply Entails.pure_left; intro hpad7
  apply Entails.pure_left; intro hinv
  match pad7, hpad7 with
  | [b1, b2, b3, b4, b5, b6, b7], _ =>
    let w_dev := pack64 g.device b1 b2 b3 b4 b5 b6 b7
    have hw_trunc : w_dev.truncate 8 = g.device :=
      pack64_truncate8 g.device b1 b2 b3 b4 b5 b6 b7
    have hpack :
        (((sp - 1240#64) ↦₈ g.device) ∗ ((sp - 1239#64) ↦ₛ [b1, b2, b3, b4, b5, b6, b7])) =
        ((sp - 1240#64) ↦₆₄ w_dev) := by
      have hcons :
          (((sp - 1240#64) ↦₈ g.device) ∗ ((sp - 1239#64) ↦ₛ [b1, b2, b3, b4, b5, b6, b7])) =
          ((sp - 1240#64) ↦ₛ [g.device, b1, b2, b3, b4, b5, b6, b7]) := by
        simp only [pointsToBytes_cons, pointsToBytes_nil, BitVec.add_assoc,
          show sp - 1240#64 + 1#64 = sp - 1239#64 by bv_omega]
      rw [hcons, pointsTo64_eq_pointsToBytes (sp - 1240#64) w_dev]
      dsimp only [w_dev, pack64]
      rw [ProofLib.unpack64_pack64]
    refine Entails.sepExists_right w_dev ?_
    apply Entails.pure_right ⟨hw_trunc, hinv⟩
    rw [hpack]
    exact Entails.refl _

theorem slot784_split_for_insert (sp : BitVec 64) :
    (memRegion (sp - 528#64) 368 ∗ memRegion (sp - 160#64) 48) =
      (∃∗ w0 : BitVec 64, ((sp - 528#64) ↦₆₄ w0)) ∗
      (∃∗ w1 : BitVec 64, ((sp - 520#64) ↦₆₄ w1)) ∗
      (∃∗ w2 : BitVec 64, ((sp - 512#64) ↦₆₄ w2)) ∗
      (∃∗ w3 : BitVec 64, ((sp - 504#64) ↦₆₄ w3)) ∗
      memRegion (sp - 496#64) 368 ∗
      memRegion (sp - 128#64) 16 := by
  have h416 :
      (memRegion (sp - 528#64) 368 ∗ memRegion (sp - 160#64) 48) =
      memRegion (sp - 528#64) 416 := by
    rw [show (416 : Nat) = 368 + 48 from rfl,
        memRegion_split (sp - 528#64) 368 48 (by decide),
        show sp - 528#64 + 368#64 = sp - 160#64 by bv_omega]
  rw [h416,
      show (416 : Nat) = 8 + 408 from rfl,
      memRegion_split (sp - 528#64) 8 408 (by decide),
      show sp - 528#64 + 8#64 = sp - 520#64 by bv_omega,
      show (408 : Nat) = 8 + 400 from rfl,
      memRegion_split (sp - 520#64) 8 400 (by decide),
      show sp - 520#64 + 8#64 = sp - 512#64 by bv_omega,
      show (400 : Nat) = 8 + 392 from rfl,
      memRegion_split (sp - 512#64) 8 392 (by decide),
      show sp - 512#64 + 8#64 = sp - 504#64 by bv_omega,
      show (392 : Nat) = 8 + 384 from rfl,
      memRegion_split (sp - 504#64) 8 384 (by decide),
      show sp - 504#64 + 8#64 = sp - 496#64 by bv_omega,
      show (384 : Nat) = 368 + 16 from rfl,
      memRegion_split (sp - 496#64) 368 16 (by decide),
      show sp - 496#64 + 368#64 = sp - 128#64 by bv_omega,
      memRegion_8_eq_pointsTo64 (sp - 528#64),
      memRegion_8_eq_pointsTo64 (sp - 520#64),
      memRegion_8_eq_pointsTo64 (sp - 512#64),
      memRegion_8_eq_pointsTo64 (sp - 504#64)]

theorem slot784_full400_eq_bytes (sp w0 w1 w2 w3 : BitVec 64) (bs368 : List (BitVec 8)) :
    (((sp - 528#64) ↦₆₄ w0) ∗ ((sp - 520#64) ↦₆₄ w1) ∗
      ((sp - 512#64) ↦₆₄ w2) ∗ ((sp - 504#64) ↦₆₄ w3) ∗
      ((sp - 496#64) ↦ₛ bs368)) =
    ((sp - 528#64) ↦ₛ (unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs368)) := by
  have e1 : sp - 528#64 + 8#64 = sp - 520#64 := by bv_omega
  have e2' : sp - 528#64 + 8#64 + 8#64 = sp - 512#64 := by bv_omega
  have e3' : sp - 528#64 + 8#64 + 8#64 + 8#64 = sp - 504#64 := by bv_omega
  have e4' : sp - 528#64 + 8#64 + 8#64 + 8#64 + 8#64 = sp - 496#64 := by bv_omega
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    ← pointsTo64_eq_pointsToBytes]
  change (((sp - 528#64) ↦₆₄ w0) ∗ ((sp - 520#64) ↦₆₄ w1) ∗
      ((sp - 512#64) ↦₆₄ w2) ∗ ((sp - 504#64) ↦₆₄ w3) ∗
      ((sp - 496#64) ↦ₛ bs368)) =
    ((sp - 528#64) ↦₆₄ w0) ∗
    (((sp - 528#64 + 8#64) ↦₆₄ w1) ∗
      (((sp - 528#64 + 8#64 + 8#64) ↦₆₄ w2) ∗
        (((sp - 528#64 + 8#64 + 8#64 + 8#64) ↦₆₄ w3) ∗
          ((sp - 528#64 + 8#64 + 8#64 + 8#64 + 8#64) ↦ₛ bs368))))
  rw [e4', e3', e2', e1]

theorem slot784_restore_from_400 (sp : BitVec 64) (bs400 : List (BitVec 8))
    (h400 : bs400.length = 400) :
    (((sp - 528#64) ↦ₛ bs400) ∗ memRegion (sp - 128#64) 16) ⊢
      memRegion (sp - 528#64) 344 ∗ memRegion (sp - 184#64) 24 ∗ memRegion (sp - 160#64) 48 := by
  have h1 := h400 ▸ pointsToBytes_entails_memRegion (sp - 528#64) bs400
  have h416 :
      (memRegion (sp - 528#64) 400 ∗ memRegion (sp - 128#64) 16) =
      memRegion (sp - 528#64) 416 := by
    rw [show (416 : Nat) = 400 + 16 from rfl,
        memRegion_split (sp - 528#64) 400 16 (by decide),
        show sp - 528#64 + 400#64 = sp - 128#64 by bv_omega]
  refine Entails.trans (sepConj_mono_left h1) ?_
  rw [h416,
      show (416 : Nat) = 344 + 72 from rfl,
      memRegion_split (sp - 528#64) 344 72 (by decide),
      show sp - 528#64 + 344#64 = sp - 184#64 by bv_omega,
      show (72 : Nat) = 24 + 48 from rfl,
      memRegion_split (sp - 184#64) 24 48 (by decide),
      show sp - 184#64 + 24#64 = sp - 160#64 by bv_omega]
  exact Entails.refl _

theorem slot48_4words_restore (sp w0 w1 w2 w3 : BitVec 64) :
    (((sp - 1264#64) ↦₆₄ w0) ∗ ((sp - 1256#64) ↦₆₄ w1) ∗
      ((sp - 1248#64) ↦₆₄ w2) ∗ ((sp - 1240#64) ↦₆₄ w3)) ⊢
    ∃∗ c72 : BitVec 8,
      memRegion (sp - 1264#64) 24 ∗ ((sp - 1240#64) ↦₈ c72) ∗ memRegion (sp - 1239#64) 7 := by
  have h24 := slot48_restore_region24 sp w0 w1 w2
  have h8 : ((sp - 1240#64) ↦₆₄ w3) ⊢
      ∃∗ c72 : BitVec 8, ((sp - 1240#64) ↦₈ c72) ∗ memRegion (sp - 1239#64) 7 := by
    refine Entails.trans (pointsTo64_entails_memRegion (sp - 1240#64) w3) ?_
    have hm8 :
        memRegion (sp - 1240#64) 8 =
        ((∃∗ c72 : BitVec 8, ((sp - 1240#64) ↦₈ c72)) ∗ memRegion (sp - 1239#64) 7) := by
      have h1 := memRegion_split (sp - 1240#64) 1 7 (by decide)
      rw [show (1 + 7 : Nat) = 8 from rfl,
          show sp - 1240#64 + 1#64 = sp - 1239#64 by bv_omega,
          memRegion_1_eq_pointsTo8 (sp - 1240#64)] at h1
      exact h1
    rw [hm8]
    simp only [sepExists_sepConj_left]
    exact Entails.refl _
  have hassoc :
      (((sp - 1264#64) ↦₆₄ w0) ∗ ((sp - 1256#64) ↦₆₄ w1) ∗
        ((sp - 1248#64) ↦₆₄ w2) ∗ ((sp - 1240#64) ↦₆₄ w3)) =
      ((((sp - 1264#64) ↦₆₄ w0) ∗ ((sp - 1256#64) ↦₆₄ w1) ∗
        ((sp - 1248#64) ↦₆₄ w2)) ∗ ((sp - 1240#64) ↦₆₄ w3)) := by ac_rfl
  rw [hassoc]
  refine Entails.trans (sepConj_mono h24 h8) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

theorem bucket_entry_of_full400_bytes (A : RustAlloc) (ctrl : BitVec 64) (k : Nat)
    (g : AddrGhost) (w_dev : BitVec 64)
    (hlen36 : g.name.bytes.length = 36)
    (hw_dev : w_dev.truncate 8 = g.device)
    (hinv : g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0)
    (recG : SessionGhost) (ss : Session (List (BitVec 8)))
    (hcanon : CanonSession recG ss)
    (bs336 : List (BitVec 8))
    (hinl : SessionInline recG ss.state (unpack64 recG.localIk.cap ++ bs336)) :
    (((bucketAddr ctrl 400 k) ↦ₛ
        (unpack64 g.name.cap ++ unpack64 g.name.ptr ++ unpack64 36#64 ++ unpack64 w_dev ++
          (unpack64 0#64 ++ (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 recG.localIk.cap ++ bs336)))) ∗
      (g.name.ptr ↦ₛ g.name.bytes) ∗
      A.live g.name.ptr g.name.cap.toNat 1 ∗
      memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
        (g.name.cap.toNat - g.name.bytes.length) ∗
      sessionAtHeap A recG ss) ⊢
    sessionBucketEntryAt A g recG ss (bucketAddr ctrl 400 k) := by
  let a := bucketAddr ctrl 400 k
  have hsplit32 :
      (a ↦ₛ
        (unpack64 g.name.cap ++ unpack64 g.name.ptr ++ unpack64 36#64 ++ unpack64 w_dev ++
          (unpack64 0#64 ++ (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 recG.localIk.cap ++ bs336)))) =
      ((a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗
        ((a + 16#64) ↦₆₄ 36#64) ∗ ((a + 24#64) ↦₆₄ w_dev) ∗
        ((a + 32#64) ↦ₛ
          (unpack64 0#64 ++ (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 recG.localIk.cap ++ bs336)))) := by
    rw [List.append_assoc (unpack64 g.name.cap ++ unpack64 g.name.ptr ++ unpack64 36#64),
        List.append_assoc (unpack64 g.name.cap ++ unpack64 g.name.ptr),
        List.append_assoc (unpack64 g.name.cap),
        pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
        pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
        pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
        pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
    have e1 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
    have e2 : a + 8#64 + 8#64 + 8#64 = a + 24#64 := by bv_omega
    have e3 : a + 8#64 + 8#64 + 8#64 + 8#64 = a + 32#64 := by bv_omega
    rw [e3, e2, e1]
  have hw_dev_split :
      ((a + 24#64) ↦₆₄ w_dev) ⊢ ((a + 24#64) ↦₈ g.device) ∗ memRegion (a + 25#64) 7 := by
    rw [pointsTo64_eq_pointsToBytes (a + 24#64) w_dev]
    have h1 : (unpack64 w_dev).length = 8 := unpack64_length w_dev
    rw [pointsToBytes_take_drop (a + 24#64) 1 (unpack64 w_dev) (by omega)]
    have htake : (unpack64 w_dev).take 1 = [g.device] := by
      rw [← hw_dev]
      rfl
    have hdrop_len : ((unpack64 w_dev).drop 1).length = 7 := by
      simp [List.length_drop, h1]
    rw [htake]
    have hpt1 : ((a + 24#64) ↦ₛ [g.device]) = ((a + 24#64) ↦₈ g.device) := by
      simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    have ha25 : a + 24#64 + BitVec.ofNat 64 1 = a + 25#64 := by bv_omega
    rw [hpt1, ha25]
    exact sepConj_mono_right (hdrop_len ▸ pointsToBytes_entails_memRegion (a + 25#64) _)
  rw [hsplit32]
  have haddr :
      ((a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗
        ((a + 16#64) ↦₆₄ 36#64) ∗ ((a + 24#64) ↦₆₄ w_dev) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        A.live g.name.ptr g.name.cap.toNat 1 ∗
        memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
          (g.name.cap.toNat - g.name.bytes.length)) ⊢
      protocolAddressAt A g a := by
    rw [protocolAddressAt_eq_of_len36 A g a hlen36]
    unfold addrRestAt
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hw_dev_split)))) ?_
    have hrhs :
        (((a + 8#64) ↦₆₄ g.name.ptr) ∗
          ((a + 16#64) ↦₆₄ 36#64) ∗
          ((a + 24#64) ↦₈ g.device) ∗
          (g.name.ptr ↦ₛ g.name.bytes) ∗
          (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
            (a ↦₆₄ g.name.cap) ∗
            A.live g.name.ptr g.name.cap.toNat 1 ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length) ∗
            memRegion (a + 25#64) 7)) =
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          ((a ↦₆₄ g.name.cap) ∗
            ((a + 8#64) ↦₆₄ g.name.ptr) ∗
            ((a + 16#64) ↦₆₄ 36#64) ∗
            (((a + 24#64) ↦₈ g.device) ∗ memRegion (a + 25#64) 7) ∗
            (g.name.ptr ↦ₛ g.name.bytes) ∗
            A.live g.name.ptr g.name.cap.toNat 1 ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length))) := by ac_rfl
    rw [hrhs]
    exact Entails.pure_right hinv (Entails.refl _)
  have hreord :
      (((a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗
          ((a + 16#64) ↦₆₄ 36#64) ∗ ((a + 24#64) ↦₆₄ w_dev) ∗
          ((a + 32#64) ↦ₛ
            (unpack64 0#64 ++ (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 recG.localIk.cap ++ bs336)))) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        A.live g.name.ptr g.name.cap.toNat 1 ∗
        memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
          (g.name.cap.toNat - g.name.bytes.length) ∗
        sessionAtHeap A recG ss) =
      (((a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗
          ((a + 16#64) ↦₆₄ 36#64) ∗ ((a + 24#64) ↦₆₄ w_dev) ∗
          (g.name.ptr ↦ₛ g.name.bytes) ∗
          A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length)) ∗
        ((a + 32#64) ↦ₛ
          (unpack64 0#64 ++ (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 recG.localIk.cap ++ bs336))) ∗
        sessionAtHeap A recG ss) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_left haddr) ?_
  exact bucket_entry_of_full368_bytes A ctrl k g recG ss hcanon bs336 hinl

theorem eval_cmlt_emptyCtrl4_getLsbD (pos : Nat) (hpos : pos < 4) :
    BitVec.truncate 64
      (0#128 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt emptyCtrl4 pos) >>> 0 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 0 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt emptyCtrl4 pos) >>> 8 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 8 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt emptyCtrl4 pos) >>> 16 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 16 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt emptyCtrl4 pos) >>> 24 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 24 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt emptyCtrl4 pos) >>> 32 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 32 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt emptyCtrl4 pos) >>> 40 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 40 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt emptyCtrl4 pos) >>> 48 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 48 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt emptyCtrl4 pos) >>> 56 &&& 255#128).getLsbD 7 = true then 255#128 else 0#128) &&& 255#128) <<< 56) =
    bv% (2 ^ 64 - 1) := by
  rw [loadGroupAt_emptyCtrl4 pos hpos]
  decide +kernel


end CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures
