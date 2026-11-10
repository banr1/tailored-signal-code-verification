/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Defs
public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-!
# Stack, `prostChainAt`, and `prostSSAt` Helpers for Seed `merge_field` Tag `7`

Provides stack-frame splitting (`0xf0`-byte frame with 104-byte temporary `Chain` slot at `sp' + 8`),
`Chain::default()` initialization, position-independent 104-byte `chunks104_6QWAt` move lemmas, and
`prostSSAt` `receiver_chains` focus lemmas for `SessionStructure::merge_field` tag `7`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stack Frame and Saved Registers -/

abbrev mfSubStack_receiverChains : Nat := 16144

/-- The 9 saved register words (plus 1 untouched word `w56` at `sp0 - 56#64`) at `[sp0 - 80#64 .. sp0)`. -/
def mfSavedRegs_receiverChains (sp0 : BitVec 64) (s0 : State) (w56 : BitVec 64) : SepProp :=
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 56#64) ↦₆₄ w56) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

/-- Untouched padding in the 240-byte stack frame outside the 104-byte `Chain` slot `[sp' + 8 .. sp' + 0x70)`
and the 80-byte saved-register area `[sp' + 0xa0 .. sp' + 0xf0)`. -/
def mfFramePad_receiverChains (sp0 : BitVec 64) : SepProp :=
  memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 128#64) 48

theorem sp_sub_240_aligned_receiverChains {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 240#64) &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt
  omega

theorem stackAt_sub_to_chainMerge_receiverChains (sp : BitVec 64) :
    stackAt sp mfSubStack_receiverChains =
      memRegion (sp - 16144#64) 3856 ∗ stackAt sp chainMergeStack := by
  change memRegion (sp - 16144#64) 16144 =
    memRegion (sp - 16144#64) 3856 ∗ memRegion (sp - 12288#64) 12288
  have h3 : (sp - 16144#64) + 3856#64 = sp - 12288#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have hsplit := memRegion_split (sp - 16144#64) 3856 12288 (by decide)
  rw [show (3856 : Nat) + 12288 = 16144 by decide,
      show BitVec.ofNat 64 3856 = 3856#64 from rfl, h3] at hsplit
  exact hsplit

theorem stackAt_sub_to_growOne_receiverChains (sp : BitVec 64) :
    stackAt sp mfSubStack_receiverChains =
      memRegion (sp - 16144#64) 11536 ∗ stackAt sp 4608 := by
  change memRegion (sp - 16144#64) 16144 =
    memRegion (sp - 16144#64) 11536 ∗ memRegion (sp - 4608#64) 4608
  have h3 : (sp - 16144#64) + 11536#64 = sp - 4608#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have hsplit := memRegion_split (sp - 16144#64) 11536 4608 (by decide)
  rw [show (11536 : Nat) + 4608 = 16144 by decide,
      show BitVec.ofNat 64 11536 = 11536#64 from rfl, h3] at hsplit
  exact hsplit

theorem memRegion80_eq_cells10_receiverChains (sp0 : BitVec 64) :
    memRegion (sp0 - 80#64) 80 =
      ∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64, ∃∗ w64 : BitVec 64, ∃∗ w56 : BitVec 64,
      ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w24 : BitVec 64,
      ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64,
        ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
        ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
        ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
        ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
        ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8) := by
  have h := LibsignalTripleRatchet.stackAt_split_cells sp0 0 10 (by decide)
  change memRegion (sp0 - 80#64) 80 =
    memRegion (sp0 - 80#64 - 0#64) 0 ∗ cells (sp0 - 80#64) 10 at h
  rw [ProofLib.memRegion_zero, emp_sepConj] at h
  rw [h]
  simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit, sepExists_sepConj_right]

theorem memRegion80_chainInit_eq_cells10_receiverChains (sp0 : BitVec 64) :
    memRegion (sp0 - 232#64) 80 =
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
      ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64,
        ((sp0 - 232#64) ↦₆₄ c0) ∗ ((sp0 - 224#64) ↦₆₄ c1) ∗
        ((sp0 - 216#64) ↦₆₄ c2) ∗ ((sp0 - 208#64) ↦₆₄ c3) ∗
        ((sp0 - 200#64) ↦₆₄ c4) ∗ ((sp0 - 192#64) ↦₆₄ c5) ∗
        ((sp0 - 184#64) ↦₆₄ c6) ∗ ((sp0 - 176#64) ↦₆₄ c7) ∗
        ((sp0 - 168#64) ↦₆₄ c8) ∗ ((sp0 - 160#64) ↦₆₄ c9) := by
  have h0 := memRegion80_eq_cells10_receiverChains (sp0 - 152#64)
  have e80 : sp0 - 152#64 - 80#64 = sp0 - 232#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e72 : sp0 - 152#64 - 72#64 = sp0 - 224#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e64 : sp0 - 152#64 - 64#64 = sp0 - 216#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e56 : sp0 - 152#64 - 56#64 = sp0 - 208#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e48 : sp0 - 152#64 - 48#64 = sp0 - 200#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e40 : sp0 - 152#64 - 40#64 = sp0 - 192#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e32 : sp0 - 152#64 - 32#64 = sp0 - 184#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e24 : sp0 - 152#64 - 24#64 = sp0 - 176#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e16 : sp0 - 152#64 - 16#64 = sp0 - 168#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e8 : sp0 - 152#64 - 8#64 = sp0 - 160#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e80, e72, e64, e56, e48, e40, e32, e24, e16, e8] at h0
  exact h0

/-- Split `stackAt sp0 mergeFieldStack` into the callee stack `stackAt (sp0 - 240#64) mfSubStack_receiverChains`,
the frame padding `mfFramePad_receiverChains sp0`, the 80-byte + 24-byte `Chain` stack slot at `sp0 - 232#64`,
and the 80-byte saved-register area at `sp0 - 80#64`. -/
theorem stackAt_mergeFieldStack_split_receiverChains (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStack =
      stackAt (sp0 - 240#64) mfSubStack_receiverChains ∗
      mfFramePad_receiverChains sp0 ∗
      memRegion (sp0 - 232#64) 80 ∗
      memRegion (sp0 - 152#64) 24 ∗
      memRegion (sp0 - 80#64) 80 := by
  change memRegion (sp0 - 16384#64) 16384 =
    memRegion (sp0 - 240#64 - 16144#64) 16144 ∗
    (memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 128#64) 48) ∗
    memRegion (sp0 - 232#64) 80 ∗
    memRegion (sp0 - 152#64) 24 ∗
    memRegion (sp0 - 80#64) 80
  have e_base : sp0 - 240#64 - 16144#64 = sp0 - 16384#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have s1 := memRegion_split (sp0 - 16384#64) 16144 240 (by decide)
  have e1 : (sp0 - 16384#64) + BitVec.ofNat 64 16144 = sp0 - 240#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (16144 : Nat) + 240 = 16384 by decide, e1] at s1
  have s2 := memRegion_split (sp0 - 240#64) 8 232 (by decide)
  have e2 : (sp0 - 240#64) + BitVec.ofNat 64 8 = sp0 - 232#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (8 : Nat) + 232 = 240 by decide, e2] at s2
  have s3 := memRegion_split (sp0 - 232#64) 80 152 (by decide)
  have e3 : (sp0 - 232#64) + BitVec.ofNat 64 80 = sp0 - 152#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (80 : Nat) + 152 = 232 by decide, e3] at s3
  have s4 := memRegion_split (sp0 - 152#64) 24 128 (by decide)
  have e4 : (sp0 - 152#64) + BitVec.ofNat 64 24 = sp0 - 128#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (24 : Nat) + 128 = 152 by decide, e4] at s4
  have s5 := memRegion_split (sp0 - 128#64) 48 80 (by decide)
  have e5 : (sp0 - 128#64) + BitVec.ofNat 64 48 = sp0 - 80#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (48 : Nat) + 80 = 128 by decide, e5] at s5
  rw [e_base, s1, s2, s3, s4, s5]
  ac_rfl

theorem stackAt_mergeFieldStack_join_receiverChains (sp0 : BitVec 64) :
    stackAt (sp0 - 240#64) mfSubStack_receiverChains ∗
      mfFramePad_receiverChains sp0 ∗
      memRegion (sp0 - 232#64) 104 ∗
      memRegion (sp0 - 80#64) 80 =
    stackAt sp0 mergeFieldStack := by
  have s := memRegion_split (sp0 - 232#64) 80 24 (by decide)
  have e : (sp0 - 232#64) + BitVec.ofNat 64 80 = sp0 - 152#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (80 : Nat) + 24 = 104 by decide, e] at s
  rw [s, stackAt_mergeFieldStack_split_receiverChains sp0]
  ac_rfl

theorem cells10_entails_memRegion80_receiverChains (sp0 : BitVec 64)
    (w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 : BitVec 64) :
    ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
      ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
      ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
      ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8) ⊢
    memRegion (sp0 - 80#64) 80 := by
  rw [memRegion80_eq_cells10_receiverChains sp0]
  exact Entails.sepExists_right w80 (Entails.sepExists_right w72
    (Entails.sepExists_right w64 (Entails.sepExists_right w56
      (Entails.sepExists_right w48 (Entails.sepExists_right w40
        (Entails.sepExists_right w32 (Entails.sepExists_right w24
          (Entails.sepExists_right w16 (Entails.sepExists_right w8 (Entails.refl _))))))))))

/-! ## `prostChainAt` Initialization and 104-Byte Move -/

theorem vecU8_nil_0_1_receiverChains (A : RustAlloc) (v : BitVec 64) :
    ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) ⊢
      vecU8 A v [] := by
  unfold vecU8 vecU8At
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_emp]
  rw [sepConj_comm (vecHeader v 0#64 1#64 0#64)]
  exact Entails.pure_right ⟨by decide, by decide, by decide⟩ (Entails.refl _)

theorem vecOf104_nil_0_8_receiverChains (A : RustAlloc) (v : BitVec 64) :
    ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) ⊢
      vecOf A 104 8 (fun (_ : Unit) _ => emp) v [] := by
  unfold vecOf vecAt vecBuf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_emp]
  rw [sepConj_comm (vecHeader v 0#64 8#64 0#64)]
  exact Entails.pure_right ⟨by decide, by decide, by decide⟩ (Entails.refl _)

/-- The 10 stores of `+0x28c .. +0x2b4` plus `memRegion (sp0 - 152#64) 24` assemble into
`prostChainAt A (sp0 - 232#64) ⟨[], [], none⟩`. -/
theorem prostChainAt_default_of_cells_receiverChains (A : RustAlloc) (sp0 : BitVec 64) :
    (((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗
      ((sp0 - 216#64) ↦₆₄ 0#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64) ∗
      ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64) ∗
      ((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 8#64) ∗
      ((sp0 - 168#64) ↦₆₄ 0#64) ∗ ((sp0 - 160#64) ↦₆₄ noneCap)) ∗
      memRegion (sp0 - 152#64) 24 ⊢
    prostChainAt A (sp0 - 232#64) ⟨[], [], none⟩ := by
  unfold prostChainAt
  dsimp only
  have e1 : (sp0 - 232#64) + 8#64 = sp0 - 224#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2 : (sp0 - 232#64) + 16#64 = sp0 - 216#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3 : (sp0 - 232#64) + 0x18#64 = sp0 - 208#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e4 : (sp0 - 208#64) + 8#64 = sp0 - 200#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e5 : (sp0 - 208#64) + 16#64 = sp0 - 192#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e6 : (sp0 - 232#64) + 0x30#64 = sp0 - 184#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e7 : (sp0 - 184#64) + 8#64 = sp0 - 176#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e8 : (sp0 - 184#64) + 16#64 = sp0 - 168#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e9 : (sp0 - 232#64) + 0x48#64 = sp0 - 160#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e10 : (sp0 - 232#64) + 0x50#64 = sp0 - 152#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e3, e6, e9, e10]
  have h1 := vecU8_nil_0_1_receiverChains A (sp0 - 232#64)
  rw [e1, e2] at h1
  have h2 := vecU8_nil_0_1_receiverChains A (sp0 - 208#64)
  rw [e4, e5] at h2
  have h3 := vecOf104_nil_0_8_receiverChains A (sp0 - 184#64)
  rw [e7, e8] at h3
  have hgrp :
      (((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗
        ((sp0 - 216#64) ↦₆₄ 0#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64) ∗
        ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64) ∗
        ((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 8#64) ∗
        ((sp0 - 168#64) ↦₆₄ 0#64) ∗ ((sp0 - 160#64) ↦₆₄ noneCap)) ∗
        memRegion (sp0 - 152#64) 24 =
      (((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64)) ∗
      (((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64)) ∗
      (((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 8#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64)) ∗
      (((sp0 - 160#64) ↦₆₄ noneCap) ∗ memRegion (sp0 - 152#64) 24) := by
    ac_rfl
  rw [hgrp]
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (Entails.refl _)))

theorem vecU8_move_bytes_receiverChains (A : RustAlloc) (a : BitVec 64) (xs : List (BitVec 8)) :
    vecU8 A a xs ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 24 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ vecU8 A b xs⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [RawByteMove.vecU8At_eq_bytes_sep_buf A a cap ptr xs]
  refine Entails.sepExists_right (vecHeaderBytes cap ptr (BitVec.ofNat 64 xs.length)) ?_
  refine Entails.sepExists_right (RustHeap.vecU8Buf A cap ptr xs) ?_
  refine Entails.pure_right ⟨by simp [vecHeaderBytes], fun b => ?_⟩ (Entails.refl _)
  rw [← RawByteMove.vecU8At_eq_bytes_sep_buf A b cap ptr xs]
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem vecOf104_move_bytes_receiverChains (A : RustAlloc) (a : BitVec 64) :
    vecOf A 104 8 (fun (_ : Unit) _ => emp) a [] ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 24 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ vecOf A 104 8 (fun (_ : Unit) _ => emp) b []⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  unfold vecOf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [RawByteMove.vecAt_eq_bytes_sep_buf A 104 8 (fun (_ : Unit) _ => emp) a cap ptr []]
  refine Entails.sepExists_right (vecHeaderBytes cap ptr (BitVec.ofNat 64 ([] : List Unit).length)) ?_
  refine Entails.sepExists_right (vecBuf A 104 8 (fun (_ : Unit) _ => emp) cap ptr []) ?_
  refine Entails.pure_right ⟨by simp [vecHeaderBytes], fun b => ?_⟩ (Entails.refl _)
  rw [← RawByteMove.vecAt_eq_bytes_sep_buf A 104 8 (fun (_ : Unit) _ => emp) b cap ptr []]
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem move_bytes_pair_receiverChains {P1 P2 : BitVec 64 → SepProp} {n1 n2 : Nat} {off : BitVec 64}
    (hoff : off = BitVec.ofNat 64 n1)
    (h1 : ∀ a : BitVec 64, P1 a ⊢
      ∃∗ bs1 : List (BitVec 8), ∃∗ H1 : SepProp,
        ⌜bs1.length = n1 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs1) ∗ H1) ⊢ P1 b⌝ ∗ (a ↦ₛ bs1) ∗ H1)
    (h2 : ∀ a : BitVec 64, P2 a ⊢
      ∃∗ bs2 : List (BitVec 8), ∃∗ H2 : SepProp,
        ⌜bs2.length = n2 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs2) ∗ H2) ⊢ P2 b⌝ ∗ (a ↦ₛ bs2) ∗ H2)
    (a : BitVec 64) :
    (P1 a ∗ P2 (a + off)) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = n1 + n2 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ (P1 b ∗ P2 (b + off))⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  refine Entails.trans (sepConj_mono (h1 a) (h2 (a + off))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro bs1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro H1
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs2
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro H2
  have hpull :
      (⌜bs1.length = n1 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs1) ∗ H1) ⊢ P1 b⌝ ∗ (a ↦ₛ bs1) ∗ H1) ∗
        (⌜bs2.length = n2 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs2) ∗ H2) ⊢ P2 b⌝ ∗
          ((a + off) ↦ₛ bs2) ∗ H2) =
      ⌜bs1.length = n1 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs1) ∗ H1) ⊢ P1 b⌝ ∗
        ⌜bs2.length = n2 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs2) ∗ H2) ⊢ P2 b⌝ ∗
        ((a ↦ₛ bs1) ∗ ((a + off) ↦ₛ bs2)) ∗ (H1 ∗ H2) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; rintro ⟨hbs1, hmov1⟩
  apply Entails.pure_left; rintro ⟨hbs2, hmov2⟩
  have ha_off : a + off = a + BitVec.ofNat 64 bs1.length := by rw [hoff, hbs1]
  rw [ha_off, ← pointsToBytes_append]
  refine Entails.sepExists_right (bs1 ++ bs2) ?_
  refine Entails.sepExists_right (H1 ∗ H2) ?_
  refine Entails.pure_right ⟨by simp [hbs1, hbs2], fun b => ?_⟩ (Entails.refl _)
  have hb_off : b + BitVec.ofNat 64 bs1.length = b + off := by rw [hoff, hbs1]
  rw [pointsToBytes_append, hb_off]
  have hgrp :
      ((b ↦ₛ bs1) ∗ ((b + off) ↦ₛ bs2)) ∗ (H1 ∗ H2) =
      ((b ↦ₛ bs1) ∗ H1) ∗ (((b + off) ↦ₛ bs2) ∗ H2) := by
    ac_rfl
  rw [hgrp]
  exact sepConj_mono (hmov1 b) (hmov2 (b + off))

/-- The 32-byte `chain_key` tail of `prostChainAt` at `a` (= `chain + 0x48`). -/
def prostCkAt_receiverChains (A : RustAlloc) (a : BitVec 64) :
    Option (BitVec 32 × List (BitVec 8)) → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 24
  | some (i, k) => vecU8 A a k ∗ ((a + 0x18#64) ↦₃₂ i) ∗ memRegion (a + 0x1c#64) 4

theorem prostCkTailSome_move_bytes_receiverChains (i : BitVec 32) (a : BitVec 64) :
    (((a ↦₃₂ i) ∗ memRegion (a + 4#64) 4) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 8 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ (((b ↦₃₂ i) ∗ memRegion (b + 4#64) 4))⌝ ∗
        (a ↦ₛ bs) ∗ H) := by
  rw [pointsTo32_eq_pointsToBytes, memRegion_eq_exists_bytes (a + 4#64) 4 (by decide),
    sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro pad
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hpad
  have h4 : a + 4#64 = a + BitVec.ofNat 64 (unpack32 i).length := rfl
  rw [h4, ← pointsToBytes_append]
  refine Entails.sepExists_right (unpack32 i ++ pad) ?_
  refine Entails.sepExists_right emp ?_
  rw [sepConj_emp]
  refine Entails.pure_right ⟨by simp [hpad], fun b => ?_⟩ (Entails.refl _)
  rw [sepConj_emp, pointsToBytes_append, unpack32_length, ← pointsTo32_eq_pointsToBytes]
  apply sepConj_mono_right
  have hm := pointsToBytes_entails_memRegion (b + 4#64) pad
  rwa [hpad] at hm

theorem prostCkAt_move_bytes_receiverChains (A : RustAlloc)
    (ck : Option (BitVec 32 × List (BitVec 8))) (a : BitVec 64) :
    prostCkAt_receiverChains A a ck ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 32 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ prostCkAt_receiverChains A b ck⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  cases ck with
  | none =>
    dsimp only [prostCkAt_receiverChains]
    rw [pointsTo64_eq_pointsToBytes, memRegion_eq_exists_bytes (a + 8#64) 24 (by decide),
      sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro pad
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpad
    have h8 : a + 8#64 = a + BitVec.ofNat 64 (unpack64 noneCap).length := rfl
    rw [h8, ← pointsToBytes_append]
    refine Entails.sepExists_right (unpack64 noneCap ++ pad) ?_
    refine Entails.sepExists_right emp ?_
    rw [sepConj_emp]
    refine Entails.pure_right ⟨by simp [hpad], fun b => ?_⟩ (Entails.refl _)
    rw [sepConj_emp, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
    apply sepConj_mono_right
    have hm := pointsToBytes_entails_memRegion (b + 8#64) pad
    rwa [hpad] at hm
  | some ik =>
    rcases ik with ⟨i, k⟩
    have heq : ∀ b : BitVec 64,
        prostCkAt_receiverChains A b (some (i, k)) =
          vecU8 A b k ∗ (((b + 0x18#64) ↦₃₂ i) ∗ memRegion ((b + 0x18#64) + 4#64) 4) := by
      intro b
      dsimp only [prostCkAt_receiverChains]
      have e1c : b + 0x18#64 + 4#64 = b + 0x1c#64 := by rw [BitVec.add_assoc]; rfl
      rw [e1c]
    have hm := move_bytes_pair_receiverChains (P1 := fun b => vecU8 A b k)
      (P2 := fun b => (b ↦₃₂ i) ∗ memRegion (b + 4#64) 4)
      (n1 := 24) (n2 := 8) (off := 0x18#64) rfl
      (fun b => vecU8_move_bytes_receiverChains A b k)
      (prostCkTailSome_move_bytes_receiverChains i) a
    simp only [show (24 : Nat) + 8 = 32 from rfl, ← heq] at hm
    exact hm

theorem prostChainAt_eq_parts_receiverChains (A : RustAlloc) (a : BitVec 64) (c : ChainV) :
    prostChainAt A a c =
      vecU8 A a c.srk ∗ vecU8 A (a + 0x18#64) c.priv ∗
      vecOf A 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
      prostCkAt_receiverChains A (a + 0x48#64) c.ck := by
  unfold prostChainAt prostCkAt_receiverChains
  have e50 : a + 0x48#64 + 8#64 = a + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have e60 : a + 0x48#64 + 0x18#64 = a + 0x60#64 := by rw [BitVec.add_assoc]; rfl
  have e64 : a + 0x48#64 + 0x1c#64 = a + 0x64#64 := by rw [BitVec.add_assoc]; rfl
  cases c.ck with
  | none =>
    dsimp only
    rw [e50]
  | some ik =>
    rcases ik with ⟨i, k⟩
    dsimp only
    rw [e60, e64]

theorem prostChainAt_move_bytes_receiverChains (A : RustAlloc) (a : BitVec 64) (c : ChainV) :
    prostChainAt A a c ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 104 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ prostChainAt A b c⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  have h12 := move_bytes_pair_receiverChains
    (P1 := fun b => vecU8 A b c.srk)
    (P2 := fun b => vecU8 A b c.priv)
    (n1 := 24) (n2 := 24) (off := 0x18#64) rfl
    (fun b => vecU8_move_bytes_receiverChains A b c.srk)
    (fun b => vecU8_move_bytes_receiverChains A b c.priv)
  have h123 := move_bytes_pair_receiverChains
    (P1 := fun b => vecU8 A b c.srk ∗ vecU8 A (b + 0x18#64) c.priv)
    (P2 := fun b => vecOf A 104 8 (fun (_ : Unit) _ => emp) b [])
    (n1 := 48) (n2 := 24) (off := 0x30#64) rfl
    h12
    (fun b => vecOf104_move_bytes_receiverChains A b)
  have h1234 := move_bytes_pair_receiverChains
    (P1 := fun b => (vecU8 A b c.srk ∗ vecU8 A (b + 0x18#64) c.priv) ∗
      vecOf A 104 8 (fun (_ : Unit) _ => emp) (b + 0x30#64) [])
    (P2 := fun b => prostCkAt_receiverChains A b c.ck)
    (n1 := 72) (n2 := 32) (off := 0x48#64) rfl
    h123
    (prostCkAt_move_bytes_receiverChains A c.ck) a
  have heq : ∀ b : BitVec 64,
      prostChainAt A b c =
        ((vecU8 A b c.srk ∗ vecU8 A (b + 0x18#64) c.priv) ∗
          vecOf A 104 8 (fun (_ : Unit) _ => emp) (b + 0x30#64) []) ∗
        prostCkAt_receiverChains A (b + 0x48#64) c.ck := by
    intro b
    rw [prostChainAt_eq_parts_receiverChains A b c]
    ac_rfl
  simp only [show (72 : Nat) + 32 = 104 from rfl, ← heq] at h1234
  exact h1234

/-- Decompose `prostChainAt A a c` into `RawByteMove.chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 ∗ H`
such that `RawByteMove.chunks104_6QWAt b q0 q1 q2 q3 q4 q5 w6 ∗ H ⊢ prostChainAt A b c` for any `b`. -/
theorem prostChainAt_move_chunks104_receiverChains (A : RustAlloc) (a : BitVec 64) (c : ChainV) :
    prostChainAt A a c ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128,
      ∃∗ q3 : BitVec 128, ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128,
      ∃∗ w6 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ b : BitVec 64,
          (RawByteMove.chunks104_6QWAt b q0 q1 q2 q3 q4 q5 w6 ∗ H) ⊢ prostChainAt A b c⌝ ∗
        RawByteMove.chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 ∗ H := by
  refine Entails.trans (prostChainAt_move_bytes_receiverChains A a c) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.sepExists_elim; intro H
  apply Entails.pure_left; rintro ⟨hlen, hmov⟩
  obtain ⟨q0, q1, q2, q3, q4, q5, w6, _, hchunks⟩ := RawByteMove.exists_bytes104Of6QW hlen
  rw [hchunks a]
  refine Entails.sepExists_right q0 (Entails.sepExists_right q1
    (Entails.sepExists_right q2 (Entails.sepExists_right q3
      (Entails.sepExists_right q4 (Entails.sepExists_right q5
        (Entails.sepExists_right w6 (Entails.sepExists_right H ?_)))))))
  refine Entails.pure_right (fun b => ?_) (Entails.refl _)
  rw [← hchunks b]
  exact hmov b

theorem chunks104_6QWAt_entails_memRegion104_receiverChains (a : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    RawByteMove.chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 ⊢ memRegion a 104 := by
  rw [RawByteMove.chunks104_6QWAt_eq_pointsToBytes]
  have hm := pointsToBytes_entails_memRegion a (RawByteMove.bytes104Of6QW q0 q1 q2 q3 q4 q5 w6)
  rwa [RawByteMove.bytes104Of6QW_length] at hm

theorem memRegion104_eq_exists_chunks104_6QWAt_receiverChains (a : BitVec 64) :
    memRegion a 104 =
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128,
      ∃∗ q3 : BitVec 128, ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128,
      ∃∗ w6 : BitVec 64,
        RawByteMove.chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 := by
  rw [memRegion_eq_exists_bytes a 104 (by decide)]
  apply RawByteMove.sepProp_eq_of_entails
  · apply Entails.sepExists_elim; intro bs
    apply Entails.pure_left; intro hlen
    obtain ⟨q0, q1, q2, q3, q4, q5, w6, _, hchunks⟩ := RawByteMove.exists_bytes104Of6QW hlen
    rw [hchunks a]
    exact Entails.sepExists_right q0 (Entails.sepExists_right q1
      (Entails.sepExists_right q2 (Entails.sepExists_right q3
        (Entails.sepExists_right q4 (Entails.sepExists_right q5
          (Entails.sepExists_right w6 (Entails.refl _)))))))
  · apply Entails.sepExists_elim; intro q0
    apply Entails.sepExists_elim; intro q1
    apply Entails.sepExists_elim; intro q2
    apply Entails.sepExists_elim; intro q3
    apply Entails.sepExists_elim; intro q4
    apply Entails.sepExists_elim; intro q5
    apply Entails.sepExists_elim; intro w6
    rw [RawByteMove.chunks104_6QWAt_eq_pointsToBytes]
    exact Entails.sepExists_right _
      (Entails.pure_right (RawByteMove.bytes104Of6QW_length q0 q1 q2 q3 q4 q5 w6) (Entails.refl _))

/-! ## `prostSSAt` `receiver_chains` Focus -/

/-- All of `prostSSAt A ss v` except the `receiver_chains` field at `ss + 0x48#64`. -/
def prostSSRest_receiverChains (A : RustAlloc) (ss : BitVec 64) (v : SSV) : SepProp :=
  vecU8 A ss v.lik ∗ vecU8 A (ss + 0x18#64) v.rik ∗ vecU8 A (ss + 0x30#64) v.root ∗
    vecU8 A (ss + 0x60#64) [] ∗ vecU8 A (ss + 0x78#64) [] ∗
    (match v.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainAt A (ss + 0x90#64) c) ∗
    (match v.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗ ((ss + 0x14c#64) ↦₃₂ 0#32) ∗ ((ss + 0x150#64) ↦₆₄ 0#64)

theorem prostSSAt_eq_recv_sep_rest_receiverChains (A : RustAlloc) (ss : BitVec 64) (v : SSV) :
    prostSSAt A ss v =
      vecOf A 104 8 (fun c a => prostChainAt A a c) (ss + 0x48#64) v.recv ∗
        prostSSRest_receiverChains A ss v := by
  unfold prostSSAt prostSSRest_receiverChains
  ac_rfl

theorem prostSSRest_apply_recv_receiverChains (A : RustAlloc) (ss : BitVec 64) (v : SSV) (c : ChainV) :
    prostSSRest_receiverChains A ss (v.apply (.recv c)) = prostSSRest_receiverChains A ss v := rfl

theorem vecAt_recv_nil_open_receiverChains (ss : BitVec 64) :
    vecOf A0 104 8 (fun c a => prostChainAt A0 a c) (ss + 0x48#64) [] ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗ ((ss + 0x58#64) ↦₆₄ 0#64) ∗
        (if cap = 0#64 then emp else memRegion ptr (cap.toNat * 104)) := by
  unfold vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  dsimp only [arrayAt, List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat]
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : ss + 0x48#64 + 16#64 = ss + 0x58#64 := by rw [BitVec.add_assoc]; rfl
  have hlive : A0.live ptr (cap.toNat * 104) 8 = emp := rfl
  rw [e50, e58, hlive, BitVec.add_zero]
  simp only [emp_sepConj]
  have hgrp :
      (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗ ((ss + 0x58#64) ↦₆₄ 0#64)) ∗
        (⌜0 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          if cap = 0#64 then emp else memRegion ptr (cap.toNat * 104)) =
      ⌜0 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗ ((ss + 0x58#64) ↦₆₄ 0#64) ∗
          if cap = 0#64 then emp else memRegion ptr (cap.toNat * 104)) := by
    ac_rfl
  rw [hgrp]
  apply Entails.pure_left
  rintro ⟨_, hlt, hptr⟩
  exact Entails.pure_right ⟨hlt, hptr⟩ (Entails.refl _)

theorem memRegion_cap_nonzero_split_receiverChains (cap ptr : BitVec 64)
    (hne0 : cap ≠ 0#64) (hcap_lt : cap.toNat * 104 < 2 ^ 63) :
    (if cap = 0#64 then emp else memRegion ptr (cap.toNat * 104)) =
      memRegion ptr 104 ∗ memRegion (ptr + 104#64) ((cap.toNat - 1) * 104) := by
  simp only [hne0, ↓reduceIte]
  have hcap1 : 1 ≤ cap.toNat := by
    have : cap.toNat ≠ 0 := fun h => hne0 (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  have hmul : cap.toNat * 104 = 104 + (cap.toNat - 1) * 104 := by omega
  have hsplit := memRegion_split ptr 104 ((cap.toNat - 1) * 104) (by omega)
  rw [← hmul, show BitVec.ofNat 64 104 = 104#64 from rfl] at hsplit
  exact hsplit

theorem growOne_cap0_pre_intro_receiverChains (ss ptr : BitVec 64) (s : State)
    (hx0 : s.readReg64 .x0 = ss + 0x48#64) (hptr : ptr ≠ 0#64) :
    ((ss + 0x48#64) ↦₆₄ 0#64) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗ stackAt s.sp 4608 ⊢
      (CryptoVerification.LibsignalSession.growOneSpec A0).pre (ss + 0x48#64, 0#64, ptr, []) s := by
  unfold CryptoVerification.LibsignalSession.growOneSpec
  dsimp only [List.length_nil, BitVec.toNat_ofNat, Nat.zero_mul]
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have hpool : A0.pool = emp := rfl
  have hif : (if (0#64 : BitVec 64) = 0 then emp else A0.live ptr 0 8 ∗ (ptr ↦ₛ [])) = emp := rfl
  rw [e50, hpool, hif]
  simp only [emp_sepConj]
  refine Entails.pure_right ⟨hx0, rfl, hptr, by decide⟩ ?_
  exact Entails.of_eq (by ac_rfl)

theorem growOne_cap0_post_elim_receiverChains (ss ptr : BitVec 64) (s0 sf : State) :
    (CryptoVerification.LibsignalSession.growOneSpec A0).post (ss + 0x48#64, 0#64, ptr, []) s0 sf ⊢
      ⌜sf.trace = s0.trace⌝ ∗
      ∃∗ p' : BitVec 64,
        ⌜(1 : Nat) ≤ (4#64 : BitVec 64).toNat ∧ (4#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        ((ss + 0x48#64) ↦₆₄ 4#64) ∗ ((ss + 0x50#64) ↦₆₄ p') ∗
        memRegion p' 104 ∗ memRegion (p' + 104#64) (((4#64 : BitVec 64).toNat - 1) * 104) ∗
        stackAt s0.sp 4608 := by
  unfold CryptoVerification.LibsignalSession.growOneSpec
  dsimp only [List.length_nil, BitVec.toNat_zero, Nat.zero_mul, Nat.mul_zero,
    Nat.sub_zero, BitVec.ofNat_eq_ofNat]
  apply Entails.pure_left; intro htr
  refine Entails.pure_right htr ?_
  apply Entails.sepExists_elim; intro p'
  refine Entails.sepExists_right p' ?_
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have hmax : max 0 4 = 4 := rfl
  have hlive : A0.live p' (max 0 4 * 104) 8 = emp := rfl
  have hpool : A0.pool = emp := rfl
  rw [e50, hlive, hpool, pointsToBytes_nil p', hmax, BitVec.add_zero]
  simp only [emp_sepConj]
  apply Entails.pure_left; intro hp'
  refine Entails.pure_right ⟨by decide, by decide, hp'⟩ ?_
  have hsplit := memRegion_split p' 104 312 (by decide)
  rw [show (104 : Nat) + 312 = 4 * 104 from rfl,
      show BitVec.ofNat 64 104 = 104#64 from rfl,
      show (312 : Nat) = ((4#64 : BitVec 64).toNat - 1) * 104 from rfl] at hsplit
  rw [hsplit]
  exact Entails.of_eq (by ac_rfl)

theorem vecAt_recv_singleton_fold_receiverChains (ss cap ptr : BitVec 64) (c : ChainV)
    (hcap1 : 1 ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗ ((ss + 0x58#64) ↦₆₄ 1#64) ∗
      prostChainAt A0 ptr c ∗ memRegion (ptr + 104#64) ((cap.toNat - 1) * 104) ⊢
    vecOf A0 104 8 (fun c a => prostChainAt A0 a c) (ss + 0x48#64) [c] := by
  have hne0 : cap ≠ 0#64 := by
    intro h0; subst h0; simp at hcap1
  have hlive : A0.live ptr (cap.toNat * 104) 8 = emp := rfl
  unfold vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  dsimp only [arrayAt, List.length_singleton, Nat.one_mul]
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : ss + 0x48#64 + 16#64 = ss + 0x58#64 := by rw [BitVec.add_assoc]; rfl
  rw [e50, e58, hlive]
  simp only [BitVec.ofNat_eq_ofNat, hne0, ↓reduceIte, emp_sepConj, sepConj_emp]
  have hgrp :
      (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗ ((ss + 0x58#64) ↦₆₄ 1#64)) ∗
        (⌜1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          (prostChainAt A0 ptr c ∗ memRegion (ptr + 104#64) ((cap.toNat - 1) * 104))) =
      ⌜1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗ ((ss + 0x58#64) ↦₆₄ 1#64) ∗
          prostChainAt A0 ptr c ∗ memRegion (ptr + 104#64) ((cap.toNat - 1) * 104)) := by
    ac_rfl
  rw [hgrp]
  exact Entails.pure_right ⟨hcap1, hcap_lt, hptr⟩ (Entails.refl _)

/-! ## Relocatable `[LibsignalPlacement]` `grow_one` Helpers -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem growOne_placed_cap0_pre_eq_receiverChains [LibsignalPlacement]
    (ss ptr sp : BitVec 64) (s : State) (hsp : s.sp = sp) :
    (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
      (CryptoVerification.LibsignalSession.growOneSpec A0)).pre
      (ss + 0x48#64, 0#64, ptr, []) s =
    ⌜LibsignalCodeRoLoaded lsmpl s.mem ∧
      (([] : List (BitVec 8)).length = (0#64).toNat * 104 ∧ s.readReg64 .x0 = ss + 0x48#64 ∧
        ptr ≠ 0#64 ∧ 8 + max (2 * (0#64).toNat) 4 * 104 ≤ 2 ^ 63)⌝ ∗
    (((ss + 0x48#64) ↦₆₄ 0#64) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗ stackAt sp 4608) := by
  unfold LibsignalTripleRatchet.withLsCodeRoLoaded CryptoVerification.LibsignalSession.growOneSpec
  dsimp only
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have hpool : A0.pool = emp := rfl
  have hif : (if (0#64 : BitVec 64) = 0 then emp else A0.live ptr ([] : List (BitVec 8)).length 8 ∗ (ptr ↦ₛ [])) = emp := rfl
  rw [sepConj_comm, e50, hpool, hif, hsp]
  simp only [emp_sepConj, pure_sepConj_pure_assoc]
  ac_rfl

theorem growOne_placed_cap0_post_elim_sp_receiverChains [LibsignalPlacement]
    (ss ptr sp : BitVec 64) (s_pre sf : State) (hsp : s_pre.sp = sp) :
    (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
      (CryptoVerification.LibsignalSession.growOneSpec A0)).post
        (ss + 0x48#64, 0#64, ptr, []) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗
      ∃∗ p' : BitVec 64,
        ⌜(1 : Nat) ≤ (4#64 : BitVec 64).toNat ∧ (4#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        ((ss + 0x48#64) ↦₆₄ 4#64) ∗ ((ss + 0x50#64) ↦₆₄ p') ∗
        memRegion p' 104 ∗ memRegion (p' + 104#64) (((4#64 : BitVec 64).toNat - 1) * 104) ∗
        stackAt sp 4608 := by
  unfold LibsignalTripleRatchet.withLsCodeRoLoaded
  dsimp only
  rw [← hsp]
  exact growOne_cap0_post_elim_receiverChains ss ptr s_pre sf

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed

