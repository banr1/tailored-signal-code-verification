/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Specifications.LibsignalSession
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionObj

/-!
# Prologue and Identity-Check Helpers (`S0Spec`) for `try_decrypt_with_state::<HookRng>`

Stack-frame initialization and `local_identity_key` / `is_same_account` call helpers for segment `S0`
(`+0x000 → +0x1d8`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem bytes4_expand (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (a ↦₃₂ pack32 b0 b1 b2 b3) =
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3)) := by
  unfold pack32
  rw [← pointsToBytes4_eq_pointsTo32 a b0 b1 b2 b3]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem bytes8_expand (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (a ↦₆₄ pack64 b0 b1 b2 b3 b4 b5 b6 b7) =
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
     ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7)) := by
  unfold pack64
  rw [← pointsToBytes8_eq_pointsTo64 a b0 b1 b2 b3 b4 b5 b6 b7]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem bytes7_groupA_eq_groupB (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    ((a ↦₃₂ pack32 b0 b1 b2 b3) ∗ ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6)) =
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₃₂ pack32 b3 b4 b5 b6)) :=
      by
  rw [bytes4_expand a b0 b1 b2 b3, bytes4_expand (a + 3#64) b3 b4 b5 b6]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem bytes9_64_8_eq_8_64 (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) :
    ((a ↦₆₄ pack64 b0 b1 b2 b3 b4 b5 b6 b7) ∗ ((a + 8#64) ↦₈ b8)) =
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ pack64 b1 b2 b3 b4 b5 b6 b7 b8)) := by
  rw [bytes8_expand a b0 b1 b2 b3 b4 b5 b6 b7, bytes8_expand (a + 1#64) b1 b2 b3 b4 b5 b6 b7 b8]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem bytes17_shift_eq (a : BitVec 64)
    (b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8) :
    ((a ↦₆₄ pack64 b6 b7 b8 b9 b10 b11 b12 b13) ∗
     ((a + 8#64) ↦₆₄ pack64 b14 b15 b16 b17 b18 b19 b20 b21) ∗
     ((a + 16#64) ↦₈ b22)) =
    ((a ↦₈ b6) ∗
     ((a + 1#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
     ((a + 9#64) ↦₆₄ pack64 b15 b16 b17 b18 b19 b20 b21 b22)) := by
  have h1 := bytes9_64_8_eq_8_64 (a + 8#64) b14 b15 b16 b17 b18 b19 b20 b21 b22
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  rw [h1, ← sepConj_assoc, bytes9_64_8_eq_8_64 a b6 b7 b8 b9 b10 b11 b12 b13 b14, sepConj_assoc]

def localGroupA (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0 w1 w2 : BitVec 64) (b31 : BitVec 8) : SepProp :=
  (a ↦₃₂ pack32 b0 b1 b2 b3) ∗
  ((a + 4#64) ↦₈ b4) ∗
  ((a + 5#64) ↦₈ b5) ∗
  ((a + 6#64) ↦₈ b6) ∗
  ((a + 7#64) ↦₆₄ w0) ∗
  ((a + 15#64) ↦₆₄ w1) ∗
  ((a + 23#64) ↦₆₄ w2) ∗
  ((a + 31#64) ↦₈ b31)

def localGroupB (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0 w1 w2 : BitVec 64) (b31 : BitVec 8) : SepProp :=
  (a ↦₈ b0) ∗
  ((a + 1#64) ↦₈ b1) ∗
  ((a + 2#64) ↦₈ b2) ∗
  ((a + 3#64) ↦₃₂ pack32 b3 b4 b5 b6) ∗
  ((a + 7#64) ↦₆₄ w0) ∗
  ((a + 15#64) ↦₆₄ w1) ∗
  ((a + 23#64) ↦₆₄ w2) ∗
  ((a + 31#64) ↦₈ b31)

theorem localGroupA_eq_localGroupB (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0 w1 w2 : BitVec 64) (b31 : BitVec 8) :
    localGroupA a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 =
    localGroupB a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 := by
  unfold localGroupA localGroupB
  rw [bytes4_expand a b0 b1 b2 b3, bytes4_expand (a + 3#64) b3 b4 b5 b6]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem exists_localGroupA_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (w0 w1 w2 : BitVec 64) (b31 : BitVec 8),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) = localGroupA a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 := by
  obtain ⟨u0, u1, u2, u3, rfl, _⟩ := exists_unpack64_of_length_32 h
  refine ⟨u0.extractLsb' 0 8, u0.extractLsb' 8 8, u0.extractLsb' 16 8, u0.extractLsb' 24 8,
          u0.extractLsb' 32 8, u0.extractLsb' 40 8, u0.extractLsb' 48 8,
          pack64 (u0.extractLsb' 56 8) (u1.extractLsb' 0 8) (u1.extractLsb' 8 8) (u1.extractLsb' 16
            8)
                 (u1.extractLsb' 24 8) (u1.extractLsb' 32 8) (u1.extractLsb' 40 8) (u1.extractLsb'
                   48 8),
          pack64 (u1.extractLsb' 56 8) (u2.extractLsb' 0 8) (u2.extractLsb' 8 8) (u2.extractLsb' 16
            8)
                 (u2.extractLsb' 24 8) (u2.extractLsb' 32 8) (u2.extractLsb' 40 8) (u2.extractLsb'
                   48 8),
          pack64 (u2.extractLsb' 56 8) (u3.extractLsb' 0 8) (u3.extractLsb' 8 8) (u3.extractLsb' 16
            8)
                 (u3.extractLsb' 24 8) (u3.extractLsb' 32 8) (u3.extractLsb' 40 8) (u3.extractLsb'
                   48 8),
          u3.extractLsb' 56 8, fun a => ?_⟩
  unfold localGroupA unpack64
  rw [bytes4_expand, bytes8_expand, bytes8_expand, bytes8_expand]
  simp only [List.cons_append, List.nil_append, pointsToBytes_cons, pointsToBytes_nil,
    sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

def remoteGroupC (a : BitVec 64) (w0 : BitVec 32) (b4 b5 : BitVec 8)
    (b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8) : SepProp :=
  (a ↦₃₂ w0) ∗
  ((a + 4#64) ↦₈ b4) ∗
  ((a + 5#64) ↦₈ b5) ∗
  ((a + 6#64) ↦₆₄ pack64 b6 b7 b8 b9 b10 b11 b12 b13) ∗
  ((a + 14#64) ↦₆₄ pack64 b14 b15 b16 b17 b18 b19 b20 b21) ∗
  ((a + 22#64) ↦₈ b22) ∗
  ((a + 23#64) ↦₆₄ w3) ∗
  ((a + 31#64) ↦₈ b31)

def remoteGroupD (a : BitVec 64) (w0 : BitVec 32) (b4 b5 : BitVec 8)
    (b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8) : SepProp :=
  (a ↦₃₂ w0) ∗
  ((a + 4#64) ↦₈ b4) ∗
  ((a + 5#64) ↦₈ b5) ∗
  ((a + 6#64) ↦₈ b6) ∗
  ((a + 7#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
  ((a + 15#64) ↦₆₄ pack64 b15 b16 b17 b18 b19 b20 b21 b22) ∗
  ((a + 23#64) ↦₆₄ w3) ∗
  ((a + 31#64) ↦₈ b31)

theorem remoteGroupC_eq_remoteGroupD (a : BitVec 64) (w0 : BitVec 32) (b4 b5 : BitVec 8)
    (b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8) :
    remoteGroupC a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 =
    remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31
      := by
  unfold remoteGroupC remoteGroupD
  rw [bytes8_expand (a + 6#64), bytes8_expand (a + 14#64),
      bytes8_expand (a + 7#64), bytes8_expand (a + 15#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem exists_remoteGroupC_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 :
      BitVec 8)
      (w3 : BitVec 64) (b31 : BitVec 8),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          remoteGroupC a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
            w3 b31 := by
  obtain ⟨u0, u1, u2, u3, rfl, _⟩ := exists_unpack64_of_length_32 h
  refine ⟨pack32 (u0.extractLsb' 0 8) (u0.extractLsb' 8 8) (u0.extractLsb' 16 8) (u0.extractLsb' 24
      8),
          u0.extractLsb' 32 8, u0.extractLsb' 40 8,
          u0.extractLsb' 48 8, u0.extractLsb' 56 8,
          u1.extractLsb' 0 8, u1.extractLsb' 8 8, u1.extractLsb' 16 8, u1.extractLsb' 24 8,
          u1.extractLsb' 32 8, u1.extractLsb' 40 8, u1.extractLsb' 48 8, u1.extractLsb' 56 8,
          u2.extractLsb' 0 8, u2.extractLsb' 8 8, u2.extractLsb' 16 8, u2.extractLsb' 24 8,
          u2.extractLsb' 32 8, u2.extractLsb' 40 8, u2.extractLsb' 48 8,
          pack64 (u2.extractLsb' 56 8) (u3.extractLsb' 0 8) (u3.extractLsb' 8 8) (u3.extractLsb' 16
            8)
                 (u3.extractLsb' 24 8) (u3.extractLsb' 32 8) (u3.extractLsb' 40 8) (u3.extractLsb'
                   48 8),
          u3.extractLsb' 56 8, fun a => ?_⟩
  unfold remoteGroupC unpack64
  rw [bytes4_expand, bytes8_expand, bytes8_expand, bytes8_expand]
  simp only [List.cons_append, List.nil_append, pointsToBytes_cons, pointsToBytes_nil,
    sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem localGroupA_401_to_B (sp : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0 w1 w2 : BitVec 64) (b31 : BitVec 8) :
    ((sp + 401#64) ↦₃₂ pack32 b0 b1 b2 b3 ∗
     (sp + 405#64) ↦₈ b4 ∗
     (sp + 406#64) ↦₈ b5 ∗
     (sp + 407#64) ↦₈ b6 ∗
     (sp + 408#64) ↦₆₄ w0 ∗
     (sp + 416#64) ↦₆₄ w1 ∗
     (sp + 424#64) ↦₆₄ w2 ∗
     (sp + 432#64) ↦₈ b31) =
    ((sp + 401#64) ↦₈ b0 ∗
     (sp + 402#64) ↦₈ b1 ∗
     (sp + 403#64) ↦₈ b2 ∗
     (sp + 404#64) ↦₃₂ pack32 b3 b4 b5 b6 ∗
     (sp + 408#64) ↦₆₄ w0 ∗
     (sp + 416#64) ↦₆₄ w1 ∗
     (sp + 424#64) ↦₆₄ w2 ∗
     (sp + 432#64) ↦₈ b31) := by
  simpa only [localGroupA, localGroupB, BitVec.add_assoc, BitVec.reduceAdd] using
    localGroupA_eq_localGroupB (sp + 401#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31

theorem localGroupA_1280_to_B (sp : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0 w1 w2 : BitVec 64) (b31 : BitVec 8) :
    ((sp + 1280#64) ↦₃₂ pack32 b0 b1 b2 b3 ∗
     (sp + 1284#64) ↦₈ b4 ∗
     (sp + 1285#64) ↦₈ b5 ∗
     (sp + 1286#64) ↦₈ b6 ∗
     (sp + 1287#64) ↦₆₄ w0 ∗
     (sp + 1295#64) ↦₆₄ w1 ∗
     (sp + 1303#64) ↦₆₄ w2 ∗
     (sp + 1311#64) ↦₈ b31) =
    ((sp + 1280#64) ↦₈ b0 ∗
     (sp + 1281#64) ↦₈ b1 ∗
     (sp + 1282#64) ↦₈ b2 ∗
     (sp + 1283#64) ↦₃₂ pack32 b3 b4 b5 b6 ∗
     (sp + 1287#64) ↦₆₄ w0 ∗
     (sp + 1295#64) ↦₆₄ w1 ∗
     (sp + 1303#64) ↦₆₄ w2 ∗
     (sp + 1311#64) ↦₈ b31) := by
  simpa only [localGroupA, localGroupB, BitVec.add_assoc, BitVec.reduceAdd] using
    localGroupA_eq_localGroupB (sp + 1280#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31

theorem adrp_0xc0_tryDecrypt_eq_logFilterAddr {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {entry : BitVec 64} (hentry : entry = img.base + 454648#64) :
    ((entry + 192#64 &&& 18446744073709547520#64) + bv% (page% (ls_sym%
      "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - 0x6f000)) + bv% ((ls_sym%
      "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      CryptoVerification.LibsignalSession.logFilterAddr img := by
  have hbal := ProofLib.base_aligned_of_loads himg
  rw [hentry, BitVec.add_assoc img.base, adrp_page_of_aligned hbal,
      CryptoVerification.LibsignalSession.logFilterAddr]
  have hmask : ((454648#64 + 192#64 : BitVec 64) &&& 18446744073709547520#64) = 454656#64 := rfl
  rw [hmask]
  bv_omega

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
