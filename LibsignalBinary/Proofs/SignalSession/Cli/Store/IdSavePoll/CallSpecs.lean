/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Layout
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Specifications.AsmConstants

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

/-- Split `memRegion out 48` into the exact cells written in `ispoll_epilogue_1bc`. -/
theorem sret48_epilogue_split (out : BitVec 64) :
    memRegion out 48 =
      (∃∗ o0 : BitVec 64, ∃∗ o8 : BitVec 32, ∃∗ o12 : BitVec 32,
       ∃∗ o16 : BitVec 64, ∃∗ o24 : BitVec 64, ∃∗ o32 : BitVec 64, ∃∗ o40 : BitVec 8,
       ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8, ∃∗ b4 : BitVec 8,
       ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8, ∃∗ b7 : BitVec 8,
        (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₃₂ o8) ∗ ((out + 12#64) ↦₃₂ o12) ∗
        ((out + 16#64) ↦₆₄ o16) ∗ ((out + 24#64) ↦₆₄ o24) ∗ ((out + 32#64) ↦₆₄ o32) ∗
        ((out + 40#64) ↦₈ o40) ∗ overlap7View1 (out + 41#64) b1 b2 b3 b4 b5 b6 b7) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 40) (b' := out + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 4) (k := 36) (b' := out + 12#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 12#64) (n := 4) (k := 32) (b' := out + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 24) (b' := out + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 16) (b' := out + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 32#64) (n := 8) (k := 8) (b' := out + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 40#64) (n := 1) (k := 7) (b' := out + 41#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight out,
      ProofLib.memRegion_four (out + 8#64),
      ProofLib.memRegion_four (out + 12#64),
      ProofLib.memRegion_eight (out + 16#64),
      ProofLib.memRegion_eight (out + 24#64),
      ProofLib.memRegion_eight (out + 32#64),
      ProofLib.memRegion_one (out + 40#64),
      memRegion_7_eq_overlap7View1 (out + 41#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_ext
  · refine Entails.sepExists_elim fun b1 => Entails.sepExists_elim fun b2 =>
      Entails.sepExists_elim fun b3 => Entails.sepExists_elim fun b4 =>
      Entails.sepExists_elim fun b5 => Entails.sepExists_elim fun b6 =>
      Entails.sepExists_elim fun b7 => Entails.sepExists_elim fun o40 =>
      Entails.sepExists_elim fun o32 => Entails.sepExists_elim fun o24 =>
      Entails.sepExists_elim fun o16 => Entails.sepExists_elim fun o12 =>
      Entails.sepExists_elim fun o8 => Entails.sepExists_elim fun o0 => ?_
    exact Entails.sepExists_right o0 (Entails.sepExists_right o8 (Entails.sepExists_right o12
      (Entails.sepExists_right o16 (Entails.sepExists_right o24 (Entails.sepExists_right o32
      (Entails.sepExists_right o40 (Entails.sepExists_right b1 (Entails.sepExists_right b2
      (Entails.sepExists_right b3 (Entails.sepExists_right b4 (Entails.sepExists_right b5
      (Entails.sepExists_right b6 (Entails.sepExists_right b7 (Entails.of_eq (by ac_rfl)))))))))))))))
  · refine Entails.sepExists_elim fun o0 => Entails.sepExists_elim fun o8 =>
      Entails.sepExists_elim fun o12 => Entails.sepExists_elim fun o16 =>
      Entails.sepExists_elim fun o24 => Entails.sepExists_elim fun o32 =>
      Entails.sepExists_elim fun o40 => Entails.sepExists_elim fun b1 =>
      Entails.sepExists_elim fun b2 => Entails.sepExists_elim fun b3 =>
      Entails.sepExists_elim fun b4 => Entails.sepExists_elim fun b5 =>
      Entails.sepExists_elim fun b6 => Entails.sepExists_elim fun b7 => ?_
    exact Entails.sepExists_right b1 (Entails.sepExists_right b2 (Entails.sepExists_right b3
      (Entails.sepExists_right b4 (Entails.sepExists_right b5 (Entails.sepExists_right b6
      (Entails.sepExists_right b7 (Entails.sepExists_right o40 (Entails.sepExists_right o32
      (Entails.sepExists_right o24 (Entails.sepExists_right o16 (Entails.sepExists_right o12
      (Entails.sepExists_right o8 (Entails.sepExists_right o0 (Entails.of_eq (by ac_rfl)))))))))))))))

def epiloguePre (s0 : State) (x : IdPollGhost)
    (c1 c2 c3 c4 c5 c6 c7 : BitVec 8) (s16 : BitVec 64) (s24 : BitVec 8) : SepProp :=
  overlap7View1 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
  ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
  ((s0.sp - 0xb8#64) ↦₈ s24) ∗
  memRegion x.call.out 48 ∗
  idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
  savedCalleeSlots s0

def epilogueOut (s0 : State) (x : IdPollGhost)
    (w0 : BitVec 64) (w8 w12 : BitVec 32) (w16 w24 : BitVec 64)
    (c1 c2 c3 c4 c5 c6 c7 : BitVec 8) (s16 : BitVec 64) (s24 : BitVec 8) : SepProp :=
  (x.call.out ↦₆₄ w0) ∗ ((x.call.out + 8#64) ↦₃₂ w8) ∗ ((x.call.out + 12#64) ↦₃₂ w12) ∗
  ((x.call.out + 16#64) ↦₆₄ w16) ∗ ((x.call.out + 24#64) ↦₆₄ w24) ∗
  ((x.call.out + 32#64) ↦₆₄ s16) ∗ ((x.call.out + 40#64) ↦₈ s24) ∗
  overlap7View2 (x.call.out + 41#64) c1 c2 c3 c4 c5 c6 c7 ∗
  overlap7View2 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
  ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
  ((s0.sp - 0xb8#64) ↦₈ s24) ∗
  idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 ∗
  savedCalleeSlots s0

theorem epilogueOut_ok_reassemble (A : RustAlloc) (out : BitVec 64) (c : IdentityChange)
    (w12 : BitVec 32) (w16 w24 s16 : BitVec 64) (s24 : BitVec 8)
    (c1 c2 c3 c4 c5 c6 c7 : BitVec 8) :
    ((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((out + 8#64) ↦₃₂ (if c == .replacedExisting then 1#32 else 0#32)) ∗
      ((out + 12#64) ↦₃₂ w12) ∗
      ((out + 16#64) ↦₆₄ w16) ∗ ((out + 24#64) ↦₆₄ w24) ∗
      ((out + 32#64) ↦₆₄ s16) ∗ ((out + 40#64) ↦₈ s24) ∗
      overlap7View2 (out + 41#64) c1 c2 c3 c4 c5 c6 c7) ⊢
      idSaveOutAt A out (.ok c) := by
  unfold idSaveOutAt
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo8_entails_memRegion _ _)
              (overlap7View2_entails_memRegion7 _ _ _ _ _ _ _ _)))))) ?_
  rw [← ProofLib.memRegion_split' (b := out + 40#64) (n := 1) (k := 7) (b' := out + 41#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 32#64) (n := 8) (k := 8) (b' := out + 40#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 16) (b' := out + 32#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 24) (b' := out + 24#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 12#64) (n := 4) (k := 32) (b' := out + 16#64) rfl (by bv_omega) (by decide),
      show out + 12#64 = out + 0xc#64 by rfl]
  exact Entails.refl _

theorem epilogueOut_err_reassemble (A : RustAlloc) (sp out : BitVec 64)
    (bs : List (BitVec 8)) (cap ptr fnPtr : BitVec 64) :
    let w5 := BitVec.ofNat 64 (utf8 "read").length
    ((out ↦₆₄ speWord 1) ∗
      ((out + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
      ((out + 12#64) ↦₃₂ cap.extractLsb' 32 32) ∗
      ((out + 16#64) ↦₆₄ ptr) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((out + 32#64) ↦₆₄ fnPtr) ∗
      ((out + 40#64) ↦₈ w5.extractLsb' 0 8) ∗
      overlap7View2 (out + 41#64) (w5.extractLsb' 8 8) (w5.extractLsb' 16 8)
        (w5.extractLsb' 24 8) (w5.extractLsb' 32 8) (w5.extractLsb' 40 8)
        (w5.extractLsb' 48 8) (w5.extractLsb' 56 8) ∗
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        if cap = 0#64 then emp
        else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
      (fnPtr ↦ᵣ utf8 "read") ∗
      ((sp - 0x90#64) ↦₆₄ speWord 1) ∗
      ((sp - 0x88#64) ↦₆₄ cap) ∗ ((sp - 0x80#64) ↦₆₄ ptr) ∗
      ((sp - 0x78#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((sp - 0x70#64) ↦₆₄ fnPtr) ∗
      ((sp - 0x68#64) ↦₆₄ w5)) ⊢
      idSaveOutAt A out (.error ()) ∗ memRegion (sp - 0x90#64) 48 := by
  intro w5
  have hcap64 : ((out + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
      ((out + 12#64) ↦₃₂ cap.extractLsb' 32 32) = ((out + 8#64) ↦₆₄ cap) := by
    rw [show out + 12#64 = (out + 8#64) + 4#64 by bv_omega, pointsTo32_pair]
    congr 1; bv_bits
  have hw5_64 := byte_overlap7View2_eq_pointsTo64 (out + 40#64) (out + 41#64) w5 (by bv_omega)
  have hout :
      ((out ↦₆₄ speWord 1) ∗
        (((out + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((out + 12#64) ↦₃₂ cap.extractLsb' 32 32)) ∗
        ((out + 16#64) ↦₆₄ ptr) ∗
        ((out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((out + 32#64) ↦₆₄ fnPtr) ∗
        (((out + 40#64) ↦₈ w5.extractLsb' 0 8) ∗
          overlap7View2 (out + 41#64) (w5.extractLsb' 8 8) (w5.extractLsb' 16 8)
            (w5.extractLsb' 24 8) (w5.extractLsb' 32 8) (w5.extractLsb' 40 8)
            (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          if cap = 0#64 then emp
          else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
        (fnPtr ↦ᵣ utf8 "read")) ⊢
      idSaveOutAt A out (.error ()) := by
    rw [hcap64, hw5_64]
    unfold idSaveOutAt speAt vecU8 vecU8At vecHeader strRefAt
    have o1 : out + asm64% spePayloadOff = out + 8#64 := by bv_omega
    have o2 : out + 8#64 + 8#64 = out + 16#64 := by bv_omega
    have o3 : out + 8#64 + 16#64 = out + 24#64 := by bv_omega
    have o4 : out + asm64% speInvalidStateFnOff = out + 32#64 := by bv_omega
    have o5 : out + 32#64 + 8#64 = out + 40#64 := by bv_omega
    rw [o1, o4]
    simp only [o2, o3, o5, sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_right fnPtr (Entails.sepExists_right bs
      (Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)))
    exact Entails.of_eq (by ac_rfl)
  have hslot :
      (((sp - 0x90#64) ↦₆₄ speWord 1) ∗
        ((sp - 0x88#64) ↦₆₄ cap) ∗ ((sp - 0x80#64) ↦₆₄ ptr) ∗
        ((sp - 0x78#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((sp - 0x70#64) ↦₆₄ fnPtr) ∗ ((sp - 0x68#64) ↦₆₄ w5)) ⊢
      memRegion (sp - 0x90#64) 48 := by
    refine Entails.trans
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (pointsTo64_entails_memRegion _ _)))))) ?_
    rw [← ProofLib.memRegion_split' (b := sp - 0x70#64) (n := 8) (k := 8) (b' := sp - 0x68#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp - 0x78#64) (n := 8) (k := 16) (b' := sp - 0x70#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp - 0x80#64) (n := 8) (k := 24) (b' := sp - 0x78#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp - 0x88#64) (n := 8) (k := 32) (b' := sp - 0x80#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp - 0x90#64) (n := 8) (k := 40) (b' := sp - 0x88#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono hout hslot)

/-! ## Discriminant, `PublicKey::eq` frame, stack arithmetic, and pure bit lemmas -/

@[arm64_norm, wp_norm]
theorem ispoll_sp_eqs (sp : BitVec 64) :
    sp + bv% (2 ^ 64 - 208) = sp - 0xd0#64 ∧
    sp - 0xd0#64 + 8#64 = sp - 0xc8#64 ∧
    sp - 0xd0#64 + 11#64 = sp - 0xc5#64 ∧
    sp - 0xc8#64 + 2#64 = sp - 0xc6#64 ∧
    sp - 0xc8#64 + 3#64 = sp - 0xc5#64 ∧
    sp - 0xc8#64 + 4#64 = sp - 0xc4#64 ∧
    sp - 0xc8#64 + 5#64 = sp - 0xc3#64 ∧
    sp - 0xd0#64 + 16#64 = sp - 0xc0#64 ∧
    sp - 0xd0#64 + 24#64 = sp - 0xb8#64 ∧
    sp - 0xd0#64 + 32#64 = sp - 0xb0#64 ∧
    sp - 0xd0#64 + 40#64 = sp - 0xa8#64 ∧
    sp - 0xd0#64 + 48#64 = sp - 0xa0#64 ∧
    sp - 0xa0#64 + 8#64 = sp - 0x98#64 ∧
    sp - 0xd0#64 + 56#64 = sp - 0x98#64 ∧
    sp - 0xd0#64 + 57#64 = sp - 0x97#64 ∧
    sp - 0x97#64 + 2#64 = sp - 0x95#64 ∧
    sp - 0x97#64 + 3#64 = sp - 0x94#64 ∧
    sp - 0x97#64 + 4#64 = sp - 0x93#64 ∧
    sp - 0x97#64 + 5#64 = sp - 0x92#64 ∧
    sp - 0xd0#64 + 60#64 = sp - 0x94#64 ∧
    sp - 0xd0#64 + 112#64 = sp - 0x60#64 ∧
    sp - 0x60#64 + 8#64 = sp - 0x58#64 ∧
    sp - 0xd0#64 + 128#64 = sp - 0x50#64 ∧
    sp - 0x50#64 + 8#64 = sp - 0x48#64 ∧
    sp - 0xd0#64 + 144#64 = sp - 0x40#64 ∧
    sp - 0x40#64 + 8#64 = sp - 0x38#64 ∧
    sp - 0xd0#64 + 160#64 = sp - 0x30#64 ∧
    sp - 0x30#64 + 8#64 = sp - 0x28#64 ∧
    sp - 0xd0#64 + 176#64 = sp - 0x20#64 ∧
    sp - 0x20#64 + 8#64 = sp - 0x18#64 ∧
    sp - 0xd0#64 + 192#64 = sp - 0x10#64 ∧
    sp - 0x10#64 + 8#64 = sp - 0x08#64 ∧
    sp - 0xd0#64 + 208#64 = sp ∧
    sp - 0x60#64 + bv% (2 ^ 64 - 48) = sp - 0x90#64 ∧
    sp - 0x60#64 + bv% (2 ^ 64 - 44) = sp - 0x8c#64 ∧
    sp - 0x60#64 + bv% (2 ^ 64 - 42) = sp - 0x8a#64 ∧
    sp - 0x60#64 + bv% (2 ^ 64 - 41) = sp - 0x89#64 ∧
    sp - 0x60#64 + bv% (2 ^ 64 - 40) = sp - 0x88#64 ∧
    sp - 0x60#64 + bv% (2 ^ 64 - 36) = sp - 0x84#64 ∧
    sp - 0x60#64 + bv% (2 ^ 64 - 34) = sp - 0x82#64 ∧
    sp - 0x60#64 + bv% (2 ^ 64 - 33) = sp - 0x81#64 ∧
    sp - 0x60#64 + bv% (2 ^ 64 - 32) = sp - 0x80#64 ∧
    sp - 0x60#64 + bv% (2 ^ 64 - 25) = sp - 0x79#64 ∧
    sp - 0x60#64 + bv% (2 ^ 64 - 17) = sp - 0x71#64 ∧
    sp - 0x60#64 + bv% (2 ^ 64 - 16) = sp - 0x70#64 ∧
    sp - 0x60#64 + bv% (2 ^ 64 - 9) = sp - 0x69#64 ∧
    sp - 0x70#64 + 8#64 = sp - 0x68#64 ∧
    sp - 0x90#64 + 4#64 = sp - 0x8c#64 ∧
    sp - 0x90#64 + 6#64 = sp - 0x8a#64 ∧
    sp - 0x90#64 + 7#64 = sp - 0x89#64 ∧
    sp - 0x90#64 + 8#64 = sp - 0x88#64 ∧
    sp - 0x90#64 + 15#64 = sp - 0x81#64 ∧
    sp - 0x90#64 + 16#64 = sp - 0x80#64 ∧
    sp - 0x90#64 + 23#64 = sp - 0x79#64 ∧
    sp - 0x90#64 + 24#64 = sp - 0x78#64 ∧
    sp - 0x90#64 + 31#64 = sp - 0x71#64 ∧
    sp - 0x90#64 + 40#64 = sp - 0x68#64 ∧
    sp - 0x88#64 + 4#64 = sp - 0x84#64 ∧
    sp - 0x88#64 + 6#64 = sp - 0x82#64 ∧
    sp - 0x88#64 + 7#64 = sp - 0x81#64 ∧
    sp - 0x88#64 + 8#64 = sp - 0x80#64 ∧
    sp - 0x88#64 + 15#64 = sp - 0x79#64 ∧
    sp - 0x88#64 + 23#64 = sp - 0x71#64 ∧
    sp - 0x88#64 + 31#64 = sp - 0x69#64 := by
  repeat' constructor <;> bv_omega

@[arm64_norm, wp_norm]
theorem out_add_eqs (out : BitVec 64) :
    out + 8#64 + 4#64 = out + 12#64 ∧
    out + 41#64 + 2#64 = out + 43#64 ∧
    out + 41#64 + 3#64 = out + 44#64 ∧
    out + 41#64 + 4#64 = out + 45#64 ∧
    out + 41#64 + 5#64 = out + 46#64 := by
  refine ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

theorem speWord_one_add_two_ne_zero : (speWord 1 + 2#64 == 0#64) = false := by
  decide

theorem okTagVec_add_two_eq_zero : (okTagVec + 2#64 == 0#64) = true := by
  decide

theorem spAligned_sub_d0 {sp0 : BitVec 64} {s : State}
    (hsp0 : sp0 &&& 15#64 = 0#64) (hsp : s.sp = sp0 - 0xd0#64) :
    s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat hsp0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢
  omega

theorem calleeSavedVRegs_writeVReg128_0 (s : State) (val : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 val) = calleeSavedVRegs s :=
  calleeSavedVRegs_writeVReg128 s 0#5 val (by decide)

theorem fs_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).fs = s.fs := by cases s; rfl
theorem fs_advancePC (s : State) : s.advancePC.fs = s.fs := by cases s; rfl
theorem fs_setMem (s : State) (m : Memory) : (s.setMem m).fs = s.fs := by cases s; rfl
theorem fs_setPState (s : State) (ps : PState) : (s.setPState ps).fs = s.fs := by cases s; rfl
theorem fs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).fs = s.fs := by
  cases s; rfl
theorem fs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).fs = s.fs := by
  cases s; rfl
theorem fs_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by cases w <;> cases s <;> rfl
theorem fs_writeVReg128 (s : State) (v : BitVec 5) (val : BitVec 128) :
    (s.writeVReg128 v val).fs = s.fs := by cases s; rfl
theorem fs_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).fs = s.fs := by cases wb <;> cases s <;> rfl

theorem stackAt_64_eq_publicKeyEq_frames (sp : BitVec 64) :
    stackAt sp 64 =
      stackFrameFor libsignalSessionImage
        "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp ∗
      stackFrameFor libsignalSessionImage
        "<[u8] as subtle::ConstantTimeEq>::ct_eq" (sp - 16#64) := by
  simp only [stackAt]
  have h64 : sp - BitVec.ofNat 64 64 = sp - 64#64 := rfl
  have h48 : sp - 16#64 - 48#64 = sp - 64#64 := by bv_omega
  rw [h64,
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 48) (k := 16)
        (b' := sp - 16#64) rfl (by bv_omega) (by decide),
      ← h48,
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.memRegion_48_eq_stackFrameFor_ct_eq (sp - 16#64),
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.memRegion_16_eq_stackFrameFor_eq sp]
  exact sepConj_comm _ _

theorem pk_pack_lo32 (w0 : BitVec 32) (h1 : BitVec 16) (b2 : BitVec 8) :
    (w0.zeroExtend 64 |||
      ((h1.zeroExtend 32 ||| (b2.zeroExtend 32 <<< 16)).zeroExtend 64 <<< 32)).truncate 32 = w0 := by
  bv_bits

theorem pk_pack_mid16 (w0 : BitVec 32) (h1 : BitVec 16) (b2 : BitVec 8) :
    (((w0.zeroExtend 64 |||
      ((h1.zeroExtend 32 ||| (b2.zeroExtend 32 <<< 16)).zeroExtend 64 <<< 32)) >>> 32)).truncate 16 = h1 := by
  bv_bits

theorem pk_pack_hi8 (w0 : BitVec 32) (h1 : BitVec 16) (b2 : BitVec 8) :
    (((w0.zeroExtend 64 |||
      ((h1.zeroExtend 32 ||| (b2.zeroExtend 32 <<< 16)).zeroExtend 64 <<< 32)) >>> 48)).truncate 8 = b2 := by
  bv_bits

theorem eor_publicKey_eq_idSaveOf (known key : IdentityKey) :
    ((if known.publicKey == key.publicKey then 1#64 else 0#64).truncate 32 ^^^ 1#32) =
      (if (if known = key then IdentityChange.newOrUnchanged else .replacedExisting) == .replacedExisting
       then 1#32 else 0#32) := by
  cases known with
  | mk pk1 =>
    cases key with
    | mk pk2 =>
      by_cases h : pk1 = pk2
      · subst h; simp
      · have hne : ¬ (IdentityKey.mk pk1 = IdentityKey.mk pk2) := fun heq => h (IdentityKey.mk.inj heq)
        simp [beq_eq_false_iff_ne.mpr h, hne]

/-! ## `SepWPp` callee combinators -/

theorem ispoll_call_panicking_raw {α : Type} {prog : Program} {img : Obj.Image}
    {callee ret_pc ret : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog callee spec)
    (x : α) (F : SepProp) {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.onPanic x s sm ∗ R') → allocFailedIn s sm ∧ s.trace <+: sm.trace)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit x code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom x s sm ∗ R'))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_wpp_frozen (x := x) (F := F) hcall hinv.1 hinv.2 hpc hrun hsp_align hlr
    ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    have hm' := Satisfies.mono (sepConj_mono_left hpre) hm
    rwa [sepConj_assoc] at hm'
  · intro sm code R' _ hpost
    exact hexit_imp code sm R' hpost
  · rintro sm _ ⟨R', hpost⟩
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using hpan_imp sm R' hpost
    exact hpan sm _ halloc0
  · intro sm hpcm hrunm hspm hcsm hfz hsym
    exact hnext sm hpcm hrunm hspm hcsm ⟨hfz, hsym⟩
  · intro sm R' _ hpost
    exact (hoom_imp sm (F ∗ R') hpost).elim

theorem ispoll_call_dirGet {prog : Program} {img : Obj.Image} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (dirGetSpec rd pathOk A img getStk))
    (xg : DirGetGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg64 .x1 = xg.self)
    (hx2 : s.readReg64 .x2 = xg.nameA) (hx3 : (s.readReg64 .x3).toNat = xg.name.length)
    (hnlen : xg.name.length < 2 ^ 32) (hdlen : xg.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf xg.dir.path xg.name))
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (dirAt A xg.self xg.dir ∗ SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
      memRegion xg.ret 48 ∗ stackAt s.sp getStk ∗ A.pool) ∗ F)
    (hnext : ∀ (sm : State) (gr : Except Unit (List (BitVec 8))),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      (gr = xg.dir.get rd s.fs.files xg.name ∧ sm.trace = s.trace) →
      SepWPp prog ret sm
        ((getResultAt A xg.ret gr ∗ dirAt A xg.self xg.dir ∗
          SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
          stackAt s.sp getStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ispoll_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [dirGetSpec, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hinv
      (Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen, hpOk⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [dirGetSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [dirGetSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [dirGetSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [dirGetSpec, Spec.inImage, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun gr => SepWPp.pure_elim fun hgr => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm gr hpcm hrunm hspm hcsm hinvm hgr)

theorem ispoll_call_decode {prog : Program} {img : Obj.Image} {A : RustAlloc}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (identityKeyDecodeSpec A img))
    (xg : DecodeGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = xg.bytesA)
    (hx1 : (s.readReg64 .x1).toNat = xg.bytes.length)
    (hx8 : s.readReg64 .x8 = xg.ret)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ ((xg.bytesA ↦ₛ xg.bytes) ∗ memRegion xg.ret 48 ∗ logOff img ∗
      stackAt s.sp 0x60) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s.trace →
      SepWPp prog ret sm
        ((identityKeyResultAt A xg.ret (decodeIdentityKey xg.bytes) ∗
          (xg.bytesA ↦ₛ xg.bytes) ∗ logOff img ∗ stackAt s.sp 0x60) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ispoll_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [identityKeyDecodeSpec, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hinv (Entails.pure_right ⟨hx0, hx1, hx8⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [identityKeyDecodeSpec, Spec.inImage] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost
    simp only [identityKeyDecodeSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [identityKeyDecodeSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [identityKeyDecodeSpec, Spec.inImage, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm htrm)

theorem ispoll_call_publicKeyEq {prog : Program} {img : Obj.Image}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee Getters.publicKeyEqSpec)
    (p1 : BitVec 64) (pk1 : PublicKey) (p2 : BitVec 64) (pk2 : PublicKey) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = p1) (hx1 : s.readReg64 .x1 = p2)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ ((p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗ stackAt s.sp 64) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) → sm.trace = s.trace →
      SepWPp prog ret sm
        (((p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗ stackAt s.sp 64) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ispoll_call_panicking_raw hcall (p1, pk1, p2, pk2, s.sp) F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [Getters.publicKeyEqSpec, ← stackAt_64_eq_publicKeyEq_frames s.sp, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, trivial⟩ (Entails.refl _)
  · intro sm R' hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [Getters.publicKeyEqSpec, ← stackAt_64_eq_publicKeyEq_frames s.sp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm hx0m htrm)

/-- Parametric-stack `PublicKey::eq` spec (`eqStk` bytes below `sp`; agrees with
`Getters.publicKeyEqSpecExt` by `rfl` at `eqStk := Getters.publicKeyEqStackExt`). -/
def publicKeyEqAtSpec (eqStk : Nat) :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
      (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
      stackAt sp eqStk
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
      stackAt sp eqStk

theorem ispoll_publicKeyEq_ok_at_64 {b : BitVec 64} {ext : String → Option (State → State)}
    (hEq : Getters.PublicKeyEqOkExt b ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr idSavePollName +
        bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
          ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      (publicKeyEqAtSpec 64) := by
  refine subroutine_ok_map (ispoll_publicKeyEq_ok_at hEq) ?_
  rintro ⟨p1, pk1, p2, pk2, sp⟩ R s0 hpre
  refine ⟨(p1, pk1, p2, pk2, sp), R, ?_, ?_⟩
  · simpa only [Getters.publicKeyEqSpec, publicKeyEqAtSpec,
      ← stackAt_64_eq_publicKeyEq_frames sp, sepConj_assoc] using hpre
  · intro sf hpost
    simpa only [Getters.publicKeyEqSpec, publicKeyEqAtSpec,
      ← stackAt_64_eq_publicKeyEq_frames sp, sepConj_assoc] using hpost

theorem ispoll_call_publicKeyEq_stk {prog : Program} {img : Obj.Image}
    {callee ret_pc ret : BitVec 64} {eqStk : Nat}
    (hcall : subroutine_ok prog callee (publicKeyEqAtSpec eqStk))
    (p1 : BitVec 64) (pk1 : PublicKey) (p2 : BitVec 64) (pk2 : PublicKey) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = p1) (hx1 : s.readReg64 .x1 = p2)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ ((p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗ stackAt s.sp eqStk) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) → sm.trace = s.trace →
      SepWPp prog ret sm
        (((p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗ stackAt s.sp eqStk) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ispoll_call_panicking_raw hcall (p1, pk1, p2, pk2, s.sp) F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [publicKeyEqAtSpec, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, trivial⟩ (Entails.refl _)
  · intro sm R' hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [publicKeyEqAtSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm hx0m htrm)

theorem ispoll_call_serialize {prog : Program} {img : Obj.Image} {A : RustAlloc}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee ((publicKeySerializeSpecX A).inImage img))
    (keyA : BitVec 64) (pk : PublicKey) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = keyA)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ ((keyA ↦ₛ pk.bytes.toList) ∗ A.pool ∗ stackAt s.sp publicKeySerializeStackX) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.readReg64 .x1 = 33#64 → sm.trace = s.trace →
      SepWPp prog ret sm
        ((boxU8Buf A (sm.readReg64 .x0) pk.serialize ∗
          (keyA ↦ₛ pk.bytes.toList) ∗ A.pool ∗ stackAt s.sp publicKeySerializeStackX) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ispoll_call_panicking_raw hcall ⟨keyA, pk⟩ F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [publicKeySerializeSpecX, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hinv (Entails.pure_right hx0 (Entails.refl _))
  · intro sm R' hpost
    simp only [publicKeySerializeSpecX, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [publicKeySerializeSpecX, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [publicKeySerializeSpecX, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [publicKeySerializeSpecX, Spec.inImage, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1m, htrm⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm hx1m htrm)

theorem ispoll_call_dirPutStr {prog : Program} {img : Obj.Image} {A : RustAlloc} {putStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (dirPutStrSpec A img putStk))
    (xg : DirPutStrGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = xg.self) (hx1 : s.readReg64 .x1 = xg.nameA)
    (hx2 : (s.readReg64 .x2).toNat = xg.name.length) (hx3 : s.readReg64 .x3 = xg.bytesV)
    (hnlen : xg.name.length < 2 ^ 32) (hdlen : xg.dir.changed.length < 2 ^ 32)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (dirAt A xg.self xg.dir ∗ SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
      vecU8 A xg.bytesV xg.bytes ∗ stackAt s.sp putStk ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s.trace →
      SepWPp prog ret sm
        ((dirAt A xg.self (xg.dir.put xg.name xg.bytes) ∗
          SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
          memRegion xg.bytesV 24 ∗ stackAt s.sp putStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ispoll_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [dirPutStrSpec, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hinv
      (Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [dirPutStrSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [dirPutStrSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [dirPutStrSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [dirPutStrSpec, Spec.inImage, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm htrm)

theorem ispoll_call_dealloc {prog : Program} {img : Obj.Image} {A : RustAlloc}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (ptr : BitVec 64) (size : Nat) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = 1) (hlay : LayoutOk size 1)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (A.pool ∗ A.live ptr size 1 ∗ memRegion ptr size ∗ stackAt s.sp extHookStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s.trace →
      SepWPp prog ret sm ((A.pool ∗ stackAt s.sp extHookStack) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ispoll_call_panicking_raw hcall (ptr, size, 1) F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [rustDeallocExternSpecWithStack, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hinv (Entails.pure_right ⟨hx0, hx1, hx2, hlay⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [rustDeallocExternSpecWithStack, Spec.inImage] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost
    simp only [rustDeallocExternSpecWithStack, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [rustDeallocExternSpecWithStack, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [rustDeallocExternSpecWithStack, Spec.inImage, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm htrm)

end CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers
