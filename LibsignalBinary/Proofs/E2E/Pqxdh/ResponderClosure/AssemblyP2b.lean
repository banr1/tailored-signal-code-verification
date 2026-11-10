/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBob
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2a
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux

/-!
# Stage P2.5 and P2.6 Layout and Error-Path Assembly for `message_decrypt_prekey::{closure#0}`

Stack-size/layout helpers and error-path assembly (`stageP2_sub6_err_ok`) for Substages P2.5 and
P2.6 of `message_decrypt_prekey::<PqxdhRng>::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.E2E.InMem
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.HashbrownBin

attribute [local irreducible] protocolAddressAt
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator

abbrev Bytes := CryptoVerification.E2E.Pqxdh.Initiator.Bytes
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## 1. Stack Size & Layout Helpers for Stage P2.5 and Stage P2.6 -/

abbrev stageP2bStack : Nat := 768 + pqxdhEntryStack

theorem exists_words4_of_len32 {bs : List (BitVec 8)} (hlen : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    u0, u1, u2, u3, _, _, _, _, h, _, _, _, _⟩ := exists_keyPair64_decomp hlen hlen
  exact ⟨u0, u1, u2, u3, h⟩

theorem exists_opkSlot65_words (tag : BitVec 8) {opkPkBytes opkSkBytes : List (BitVec 8)}
    (hpk : opkPkBytes.length = 32) (hsk : opkSkBytes.length = 32) :
    ∃ (opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7 : BitVec 64) (opk_b64 : BitVec 8),
      ∀ a : BitVec 64,
        (a ↦₈ tag) ∗ ((a + 1#64) ↦ₛ opkPkBytes) ∗ ((a + 33#64) ↦ₛ opkSkBytes) =
          (a ↦₆₄ opk0) ∗ ((a + 0x8#64) ↦₆₄ opk1) ∗ ((a + 0x10#64) ↦₆₄ opk2) ∗
          ((a + 0x18#64) ↦₆₄ opk3) ∗ ((a + 0x20#64) ↦₆₄ opk4) ∗ ((a + 0x28#64) ↦₆₄ opk5) ∗
          ((a + 0x30#64) ↦₆₄ opk6) ∗ ((a + 0x38#64) ↦₆₄ opk7) ∗ ((a + 0x40#64) ↦₈ opk_b64) := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b63, _, _, _, _, _, _, _,
    w0, w1, w2, w3, w4, w5, w6, _, _, _, _, _, _, _, _, _, _, hkp, _, _⟩ :=
    exists_keyPair64_decomp hpk hsk
  obtain ⟨opk0, hopk0⟩ := point8_bytes7At_eq_pointsTo64 tag b0 b1 b2 b3 b4 b5 b6
  refine ⟨opk0, w0, w1, w2, w3, w4, w5, w6, b63, fun a => ?_⟩
  have h1 := hkp (a + 1#64)
  rw [show a + 1#64 + 32#64 = a + 33#64 by bv_omega] at h1
  rw [h1]
  exact point8_keyPair64UnalignedAt_eq_words8_byte tag b0 b1 b2 b3 b4 b5 b6 b63
    w0 w1 w2 w3 w4 w5 w6 opk0 hopk0 a

def opkPresentTag (opkBSk? : Option Bytes) : BitVec 8 :=
  if (match opkBSk? with | some _ => true | none => false) = true then 1#8 else 0#8

def opkOptFieldAt (a : BitVec 64) (opkBSk? : Option Bytes) : SepProp :=
  match opkBSk? with
  | some opkSk => (a ↦ₛ bytesToBv8 opkSk)
  | none => .emp

def opkUnusedFieldAt (a : BitVec 64) (opkBSk? : Option Bytes) (opkSkBytes : List (BitVec 8)) :
  SepProp :=
  match opkBSk? with
  | some _ => .emp
  | none => (a ↦ₛ opkSkBytes)

theorem opkSlot65_eq_optField (a : BitVec 64) (opkBSk? : Option Bytes)
    (opkSkBytes : List (BitVec 8)) :
    (∀ opkSk, opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk) →
    (a ↦ₛ opkSkBytes) =
      opkOptFieldAt a opkBSk? ∗
      opkUnusedFieldAt a opkBSk? opkSkBytes := by
  intro h
  unfold opkOptFieldAt opkUnusedFieldAt
  cases opkBSk? with
  | none => simp [emp_sepConj]
  | some opkSk => simp [h opkSk rfl, sepConj_emp]

theorem words4_entails_cells4 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      cells a 4 := by
  simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.refl _))))

theorem words8_entails_cells8 (a w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
    ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ⊢
      cells a 8 := by
  simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5
        (Entails.sepExists_right w6 (Entails.sepExists_right w7 (Entails.refl _))))))))

theorem words8_entails_memRegion64 (a w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
    ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ⊢
      memRegion a 64 := by
  rw [ProofLib.memRegion_cells a 8 (by decide)]
  exact words8_entails_cells8 a w0 w1 w2 w3 w4 w5 w6 w7

theorem bobParamsFieldsAt_intro (coroPtr msgPtr kyberKpSecPtr ctBufPtr : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes) :
    ((coroPtr + 0x658#64) ↦ₛ bytesToBv8 ikBPk) ∗ ((coroPtr + 0x678#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
    ((coroPtr + 0x6b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
    ((coroPtr + 0x6d8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
    ((coroPtr + 0x6f8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗ ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
    ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗ ((coroPtr + 0x738#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
    ((coroPtr + 0x740#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
    opkOptFieldAt (coroPtr + 0x761#64) inp.opkBSk? ∗
    (kyberKpSecPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
    ((kyberKpSecPtr + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗
      ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗
    ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗ (ctBufPtr ↦₈ 8#8) ∗
    ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
    ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗ ((coroPtr + 0x781#64) ↦₈ 0#8) ∗
    ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
    ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) =
      bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
        (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 := by
  unfold bobParamsFieldsAt pqxdhAcceptOptFieldsAt opkPresentTag opkOptFieldAt
  have h1 : (coroPtr + 0x658#64) + 32#64 = coroPtr + 0x678#64 := by bv_omega
  have h2 : (coroPtr + 0x658#64) + 96#64 = coroPtr + 0x6b8#64 := by bv_omega
  have h3 : (coroPtr + 0x658#64) + 128#64 = coroPtr + 0x6d8#64 := by bv_omega
  have h4 : (coroPtr + 0x658#64) + 160#64 = coroPtr + 0x6f8#64 := by bv_omega
  have h5 : (coroPtr + 0x658#64) + 208#64 = coroPtr + 0x728#64 := by bv_omega
  have h6 : (coroPtr + 0x658#64) + 216#64 = coroPtr + 0x730#64 := by bv_omega
  have h7 : (coroPtr + 0x658#64) + 224#64 = coroPtr + 0x738#64 := by bv_omega
  have h8 : (coroPtr + 0x658#64) + 232#64 = coroPtr + 0x740#64 := by bv_omega
  have h9 : (coroPtr + 0x658#64) + 265#64 = coroPtr + 0x761#64 := by bv_omega
  have h10 : (coroPtr + 0x658#64) + 297#64 = coroPtr + 0x781#64 := by bv_omega
  have h11 : (coroPtr + 0x398#64) + 32#64 = coroPtr + 0x3b8#64 := by bv_omega
  have h12 : (msgPtr + 0x90#64) + 8#64 = msgPtr + 0x98#64 := by bv_omega
  have h3168 : (0xc60#64 : BitVec 64) = 3168#64 := rfl
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h3168]
  ac_rfl

/-! ## 2. Substage P2.6 (`+0x125c#64 -> +0x1778#64`) -/

theorem pqsk_entails_memRegion3168 (pqskPtr : BitVec 64) (pqspkBSk : Bytes)
    (hlen : pqspkBSk.length = 3168) :
    (pqskPtr ↦₈ (bytesToBv8 pqspkBSk).getD 0 0#8) ∗
    ((pqskPtr + 1#64) ↦ₛ (bytesToBv8 pqspkBSk).drop 1) ⊢
      memRegion pqskPtr 3168 :=
  pqsk_entails_memRegion_3168 pqskPtr pqspkBSk hlen

theorem cells6_250_fold (coroPtr w0 w1 w2 w4 w5 : BitVec 64) (w3_lo w3_hi : BitVec 32) :
    ((coroPtr + 0x250#64) ↦₆₄ w0) ∗ ((coroPtr + 0x258#64) ↦₆₄ w1) ∗
    ((coroPtr + 0x260#64) ↦₆₄ w2) ∗ ((coroPtr + 0x268#64) ↦₃₂ w3_lo) ∗
    ((coroPtr + 0x26c#64) ↦₃₂ w3_hi) ∗ ((coroPtr + 0x270#64) ↦₆₄ w4) ∗
    ((coroPtr + 0x278#64) ↦₆₄ w5) ⊢
      cells (coroPtr + 0x250#64) 6 := by
  rw [← ProofLib.memRegion_cells (coroPtr + 0x250#64) 6 (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x250#64) (n := 8) (k := 40)
        (b' := coroPtr + 0x258#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x258#64) (n := 8) (k := 32)
        (b' := coroPtr + 0x260#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x260#64) (n := 8) (k := 24)
        (b' := coroPtr + 0x268#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x268#64) (n := 4) (k := 20)
        (b' := coroPtr + 0x26c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x26c#64) (n := 4) (k := 16)
        (b' := coroPtr + 0x270#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x270#64) (n := 8) (k := 8)
        (b' := coroPtr + 0x278#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _
      _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _) (sepConj_mono (pointsTo32_entails_memRegion _
      _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))))

theorem initBobErrAt_entails (sp : BitVec 64) :
    initBobErrAt (sp + 0x3e0#64) ⊢
      ∃∗ errTag : BitVec 64,
        ⌜errTag ≠ 0xfffffffffffffffe#64 ∧ errTag ≠ 0xfffffffffffffffd#64⌝ ∗
        ((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((sp + 0x3e8#64) ↦₆₄ errTag) ∗
        memRegion (sp + 0x3f0#64) 328 := by
  unfold initBobErrAt pollReadyOkWord
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun errTag => Entails.sepExists_right errTag ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.E2E.Pqxdh.ResponderClosure
