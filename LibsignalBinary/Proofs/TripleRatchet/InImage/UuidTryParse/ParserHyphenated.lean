/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.DecodeHex32
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Simple and Hyphenated Branches of `uuid::parser::try_parse`

Defines the 17-byte `Result<[u8; 16], InvalidUuid>` layout `parserTryParseResultAt` and verifies
the 32-byte simple and 36-byte hyphenated branches of `uuid::parser::try_parse`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
  CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## UUID word packing and `parser::try_parse` contract -/

def uuidWord0 (u : List.Vector (BitVec 8) 16) : BitVec 64 :=
  pack64 (u.toList.getD 0 0#8) (u.toList.getD 1 0#8) (u.toList.getD 2 0#8) (u.toList.getD 3 0#8)
    (u.toList.getD 4 0#8) (u.toList.getD 5 0#8) (u.toList.getD 6 0#8) (u.toList.getD 7 0#8)

def uuidWord1 (u : List.Vector (BitVec 8) 16) : BitVec 64 :=
  pack64 (u.toList.getD 8 0#8) (u.toList.getD 9 0#8) (u.toList.getD 10 0#8) (u.toList.getD 11 0#8)
    (u.toList.getD 12 0#8) (u.toList.getD 13 0#8) (u.toList.getD 14 0#8) (u.toList.getD 15 0#8)

theorem pointsToBytes_uuid (a : BitVec 64) (u : List.Vector (BitVec 8) 16) :
    (a ↦ₛ u.toList) = ((a ↦₆₄ uuidWord0 u) ∗ ((a + 8#64) ↦₆₄ uuidWord1 u)) := by
  have hlen : u.toList.length = 16 := u.toList_length
  have hsplit : u.toList = (u.toList.drop 0).take 8 ++ (u.toList.drop 8).take 8 := by
    have hd : (u.toList.drop 8).length ≤ 8 := by simp [hlen]
    simp only [List.drop_zero, List.take_of_length_le hd, List.take_append_drop]
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append]
  have ht8 : ((u.toList.drop 0).take 8).length = 8 := by simp [hlen]
  rw [ht8, pointsToBytes_take8_eq_pointsTo64 a u.toList 0 (by omega),
    pointsToBytes_take8_eq_pointsTo64 (a + 8#64) u.toList 8 (by omega)]
  rfl

/-- The 17-byte `Result<[u8; 16], InvalidUuid>` written by `uuid::parser::try_parse` (`0x4930c`)
at `out17` (`x8`):
- `some u`: 16 UUID bytes at `out17..out17+16`, tag byte `0xff` at `out17+16`;
- `none`: 16 bytes at `out17..out17+16` (error slice/offset), tag byte `≠ 0xff` (`0` or `2`) at `out17+16`. -/
def parserTryParseResultAt (out17 : BitVec 64) : Option (List.Vector (BitVec 8) 16) → SepProp
  | some u => (out17 ↦ₛ u.toList) ∗ ((out17 + 16#64) ↦₈ 0xff#8)
  | none =>
    (∃∗ w0 : BitVec 64, out17 ↦₆₄ w0) ∗
    (∃∗ w1 : BitVec 64, (out17 + 8#64) ↦₆₄ w1) ∗
    (∃∗ tag : BitVec 8, ⌜tag ≠ 0xff#8⌝ ∗ ((out17 + 16#64) ↦₈ tag))

def parserTryParseSpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p, bs, out17) s =>
    (⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out17⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out17 17) ∗ stackAt s.sp 0x80
  post := fun (p, bs, out17) s0 sf =>
    (⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗ parserTryParseResultAt out17 (uuidTryParse bs)) ∗ stackAt s0.sp 0x80

theorem decodeHex32_ok_from_parser (b : BitVec 64)
    (hooks : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr parserTryParseName + bv% (2 ^ 64 + (ls_off% "uuid::parser::decode_hex32") - (ls_off% "uuid::parser::try_parse")))
      decodeHex32Spec := by
  have h : (libsignalSessionCode.rebase b hooks).fnAddr parserTryParseName + bv% (2 ^ 64 + (ls_off% "uuid::parser::decode_hex32") - (ls_off% "uuid::parser::try_parse")) =
      (libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name := by
    simp only [Program.fnAddr_rebase, parserTryParseName, decodeHex32Name,
      (ls_lemma% fnOff "uuid::parser::try_parse"), (ls_lemma% fnOff "uuid::parser::decode_hex32")]
    bv_arith
  rw [h]
  exact decodeHex32_ok b hooks

/-! ## Pure decomposition of 36-byte hyphenated inputs -/

theorem exists_word64_of_length_8 (s : List (BitVec 8)) (h : s.length = 8) :
    ∃ w : BitVec 64, ∀ a : BitVec 64, (a ↦ₛ s) = (a ↦₆₄ w) := by
  rcases list_length_8_elim s h with ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩
  exact ⟨pack64 b0 b1 b2 b3 b4 b5 b6 b7,
    fun a => pointsToBytes8_eq_pointsTo64 a b0 b1 b2 b3 b4 b5 b6 b7⟩

theorem exists_word32_of_length_4 (s : List (BitVec 8)) (h : s.length = 4) :
    ∃ w : BitVec 32, ∀ a : BitVec 64, (a ↦ₛ s) = (a ↦₃₂ w) := by
  rcases s with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try (simp at h)
  exact ⟨b3 ++ b2 ++ b1 ++ b0, fun a => pointsToBytes4_eq_pointsTo32 a b0 b1 b2 b3⟩

theorem drop_eq_take_append_cons_drop (s : List (BitVec 8)) (i m : Nat) (h : i + m < s.length) :
    s.drop i = (s.drop i).take m ++ ([s[i + m]] ++ s.drop (i + m + 1)) := by
  conv => lhs; rw [← List.take_append_drop m (s.drop i)]
  rw [List.drop_drop, List.drop_eq_getElem_cons h]
  rfl

theorem exists_36_parts (s : List (BitVec 8)) (h : s.length = 36) :
    ∃ (hex32 : List (BitVec 8)) (b8 b13 b18 b23 : BitVec 8)
      (w0 w4 : BitVec 64) (w1 w2 w3 w5 : BitVec 32),
      hex32.length = 32 ∧
      s[8]? = some b8 ∧ s[13]? = some b13 ∧ s[18]? = some b18 ∧ s[23]? = some b23 ∧
      s.take 8 ++ (s.drop 9).take 4 ++ (s.drop 14).take 4 ++ (s.drop 19).take 4 ++ s.drop 24 = hex32 ∧
      (∀ p : BitVec 64,
        (p ↦ₛ s) =
          (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₈ b8) ∗ ((p + 9#64) ↦₃₂ w1) ∗
          ((p + 13#64) ↦₈ b13) ∗ ((p + 14#64) ↦₃₂ w2) ∗ ((p + 18#64) ↦₈ b18) ∗
          ((p + 19#64) ↦₃₂ w3) ∗ ((p + 23#64) ↦₈ b23) ∗ ((p + 24#64) ↦₆₄ w4) ∗
          ((p + 32#64) ↦₃₂ w5)) ∧
      (∀ sp : BitVec 64,
        (((sp - 88#64) ↦₆₄ w0) ∗ ((sp - 80#64) ↦₃₂ w1) ∗ ((sp - 76#64) ↦₃₂ w2) ∗
         ((sp - 72#64) ↦₃₂ w3) ∗ ((sp - 68#64) ↦₆₄ w4) ∗ ((sp - 60#64) ↦₃₂ w5)) =
        ((sp - 88#64) ↦ₛ hex32)) := by
  let s0 := s.take 8
  let b8 := s[8]'(by omega)
  let s1 := (s.drop 9).take 4
  let b13 := s[13]'(by omega)
  let s2 := (s.drop 14).take 4
  let b18 := s[18]'(by omega)
  let s3 := (s.drop 19).take 4
  let b23 := s[23]'(by omega)
  let s4 := (s.drop 24).take 8
  let s5 := s.drop 32
  have hs0 : s0.length = 8 := by simp [s0, h]
  have hs1 : s1.length = 4 := by simp [s1, h]
  have hs2 : s2.length = 4 := by simp [s2, h]
  have hs3 : s3.length = 4 := by simp [s3, h]
  have hs4 : s4.length = 8 := by simp [s4, h]
  have hs5 : s5.length = 4 := by simp [s5, h]
  rcases exists_word64_of_length_8 s0 hs0 with ⟨w0, hw0⟩
  rcases exists_word32_of_length_4 s1 hs1 with ⟨w1, hw1⟩
  rcases exists_word32_of_length_4 s2 hs2 with ⟨w2, hw2⟩
  rcases exists_word32_of_length_4 s3 hs3 with ⟨w3, hw3⟩
  rcases exists_word64_of_length_8 s4 hs4 with ⟨w4, hw4⟩
  rcases exists_word32_of_length_4 s5 hs5 with ⟨w5, hw5⟩
  have hs24 : s.drop 24 = s4 ++ s5 := by
    dsimp only [s4, s5]
    rw [show (32 : Nat) = 24 + 8 from rfl, ← List.drop_drop, List.take_append_drop]
  let hex32 := s0 ++ (s1 ++ (s2 ++ (s3 ++ (s4 ++ s5))))
  have hhex_eq : s.take 8 ++ (s.drop 9).take 4 ++ (s.drop 14).take 4 ++ (s.drop 19).take 4 ++ s.drop 24 = hex32 := by
    simp only [s0, s1, s2, s3, hs24, hex32, List.append_assoc]
  have hhex_len : hex32.length = 32 := by
    simp only [hex32, List.length_append, hs0, hs1, hs2, hs3, hs4, hs5]
  have hs_decomp : s = s0 ++ ([b8] ++ (s1 ++ ([b13] ++ (s2 ++ ([b18] ++ (s3 ++ ([b23] ++ (s4 ++ s5)))))))) := by
    have e1 : s = s0 ++ ([b8] ++ s.drop 9) :=
      drop_eq_take_append_cons_drop s 0 8 (by omega)
    have e2 : s.drop 9 = s1 ++ ([b13] ++ s.drop 14) :=
      drop_eq_take_append_cons_drop s 9 4 (by omega)
    have e3 : s.drop 14 = s2 ++ ([b18] ++ s.drop 19) :=
      drop_eq_take_append_cons_drop s 14 4 (by omega)
    have e4 : s.drop 19 = s3 ++ ([b23] ++ s.drop 24) :=
      drop_eq_take_append_cons_drop s 19 4 (by omega)
    rw [e1, e2, e3, e4, hs24]
  refine ⟨hex32, b8, b13, b18, b23, w0, w4, w1, w2, w3, w5, hhex_len,
    List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
    hhex_eq, ?_, ?_⟩
  · intro p
    conv => lhs; rw [hs_decomp]
    rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
        pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
        pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
    simp only [hs0, hs1, hs2, hs3, hs4, List.length_singleton,
      hw0, hw1, hw2, hw3, hw4, hw5, pointsToBytes_singleton,
      BitVec.add_assoc, BitVec.reduceAdd]
  · intro sp
    symm
    dsimp only [hex32]
    rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
        pointsToBytes_append, pointsToBytes_append]
    simp only [hs0, hs1, hs2, hs3, hs4, hw0, hw1, hw2, hw3, hw4, hw5, arm64_norm]

theorem parseHyphenated_of_parts (s hex32 : List (BitVec 8)) (b8 b13 b18 b23 : BitVec 8)
    (hlen : s.length = 36)
    (hb8 : s[8]? = some b8) (hb13 : s[13]? = some b13)
    (hb18 : s[18]? = some b18) (hb23 : s[23]? = some b23)
    (hhex : s.take 8 ++ (s.drop 9).take 4 ++ (s.drop 14).take 4 ++ (s.drop 19).take 4 ++ s.drop 24 = hex32) :
    parseHyphenated s =
      if b8 = 0x2d#8 ∧ b13 = 0x2d#8 ∧ b18 = 0x2d#8 ∧ b23 = 0x2d#8 then
        decodeHex32 hex32
      else none := by
  unfold parseHyphenated hyphen
  simp only [hlen, hb8, hb13, hb18, hb23, hhex, Option.some.injEq, true_and]

theorem parseHyphenated_ne_8 {s hex32 : List (BitVec 8)} {b8 b13 b18 b23 : BitVec 8}
    (hp : parseHyphenated s = if b8 = 0x2d#8 ∧ b13 = 0x2d#8 ∧ b18 = 0x2d#8 ∧ b23 = 0x2d#8 then decodeHex32 hex32 else none)
    (hne : BitVec.zeroExtend 32 b8 ≠ 45#32) :
    parseHyphenated s = none := by
  have : b8 ≠ 0x2d#8 := fun h => hne (by subst h; rfl)
  simp [hp, this]

theorem parseHyphenated_ne_13 {s hex32 : List (BitVec 8)} {b8 b13 b18 b23 : BitVec 8}
    (hp : parseHyphenated s = if b8 = 0x2d#8 ∧ b13 = 0x2d#8 ∧ b18 = 0x2d#8 ∧ b23 = 0x2d#8 then decodeHex32 hex32 else none)
    (hne : BitVec.zeroExtend 32 b13 ≠ 45#32) :
    parseHyphenated s = none := by
  have : b13 ≠ 0x2d#8 := fun h => hne (by subst h; rfl)
  simp [hp, this]

theorem parseHyphenated_ne_18 {s hex32 : List (BitVec 8)} {b8 b13 b18 b23 : BitVec 8}
    (hp : parseHyphenated s = if b8 = 0x2d#8 ∧ b13 = 0x2d#8 ∧ b18 = 0x2d#8 ∧ b23 = 0x2d#8 then decodeHex32 hex32 else none)
    (hne : BitVec.zeroExtend 32 b18 ≠ 45#32) :
    parseHyphenated s = none := by
  have : b18 ≠ 0x2d#8 := fun h => hne (by subst h; rfl)
  simp [hp, this]

theorem parseHyphenated_ne_23 {s hex32 : List (BitVec 8)} {b8 b13 b18 b23 : BitVec 8}
    (hp : parseHyphenated s = if b8 = 0x2d#8 ∧ b13 = 0x2d#8 ∧ b18 = 0x2d#8 ∧ b23 = 0x2d#8 then decodeHex32 hex32 else none)
    (hne : BitVec.zeroExtend 32 b23 ≠ 45#32) :
    parseHyphenated s = none := by
  have : b23 ≠ 0x2d#8 := fun h => hne (by subst h; rfl)
  simp [hp, this]

theorem byte_eq_of_zext64_eq {b : BitVec 8} {c : BitVec 8}
    (h : BitVec.zeroExtend 64 b = BitVec.zeroExtend 64 c) : b = c := by
  revert h; bv_omega

theorem parseHyphenated_all_eq {s hex32 : List (BitVec 8)} {b8 b13 b18 b23 : BitVec 8}
    (hp : parseHyphenated s = if b8 = 0x2d#8 ∧ b13 = 0x2d#8 ∧ b18 = 0x2d#8 ∧ b23 = 0x2d#8 then decodeHex32 hex32 else none)
    (h8 : BitVec.zeroExtend 64 b8 = 45#64)
    (h13 : BitVec.zeroExtend 64 b13 = 45#64)
    (h18 : BitVec.zeroExtend 64 b18 = 45#64)
    (h23 : BitVec.zeroExtend 64 b23 = 45#64) :
    parseHyphenated s = decodeHex32 hex32 := by
  have e8 : b8 = 0x2d#8 := byte_eq_of_zext64_eq h8
  have e13 : b13 = 0x2d#8 := byte_eq_of_zext64_eq h13
  have e18 : b18 = 0x2d#8 := byte_eq_of_zext64_eq h18
  have e23 : b23 = 0x2d#8 := byte_eq_of_zext64_eq h23
  simp [hp, e8, e13, e18, e23]

/-! ## Stack and buffer layout splits for `uuid::parser::try_parse` (`0x4930c`) -/

theorem memRegion_out17_split (out17 : BitVec 64) :
    memRegion out17 17 =
      (∃∗ w0 : BitVec 64, out17 ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (out17 + 8#64) ↦₆₄ w1) ∗
      (∃∗ b2 : BitVec 8, (out17 + 16#64) ↦₈ b2) := by
  rw [ProofLib.memRegion_split' (b := out17) (n := 8) (k := 9)
        (b' := out17 + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := out17 + 8#64) (n := 8) (k := 1)
        (b' := out17 + 16#64) rfl (by bv_arith) (by decide),
      memRegion_eight out17, memRegion_eight (out17 + 8#64), memRegion_one (out17 + 16#64)]

theorem parserTryParseResultAt_some_eq (out17 : BitVec 64) (u : List.Vector (BitVec 8) 16) :
    parserTryParseResultAt out17 (some u) =
      (out17 ↦₆₄ uuidWord0 u) ∗ ((out17 + 8#64) ↦₆₄ uuidWord1 u) ∗ ((out17 + 16#64) ↦₈ 0xff#8) := by
  simp only [parserTryParseResultAt, pointsToBytes_uuid out17 u, sepConj_assoc]

theorem stackAt_parser_split (sp : BitVec 64) :
    stackAt sp 0x80 =
      stackAt (sp - 96#64) 0x20 ∗
      memRegion (sp - 96#64) 8 ∗
      memRegion (sp - 88#64) 32 ∗
      memRegion (sp - 56#64) 4 ∗
      memRegion (sp - 52#64) 17 ∗
      memRegion (sp - 35#64) 3 ∗
      (∃∗ s29 : BitVec 64, (sp - 32#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 24#64) ↦₆₄ s30) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0x80 = 128#64 from rfl,
      show sp - 96#64 - BitVec.ofNat 64 0x20 = sp - 128#64 by bv_arith,
      ProofLib.memRegion_split' (b := sp - 128#64) (n := 32) (k := 96)
        (b' := sp - 96#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 88)
        (b' := sp - 88#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 32) (k := 56)
        (b' := sp - 56#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 4) (k := 52)
        (b' := sp - 52#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 52#64) (n := 17) (k := 35)
        (b' := sp - 35#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 35#64) (n := 3) (k := 32)
        (b' := sp - 32#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp - 32#64), memRegion_eight (sp - 24#64),
      memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]

theorem memRegion_sp88_32_for_hyphen (sp : BitVec 64) :
    memRegion (sp - 88#64) 32 =
      (∃∗ t0 : BitVec 64, (sp - 88#64) ↦₆₄ t0) ∗
      (∃∗ t1 : BitVec 32, (sp - 80#64) ↦₃₂ t1) ∗
      (∃∗ t2 : BitVec 32, (sp - 76#64) ↦₃₂ t2) ∗
      (∃∗ t3 : BitVec 32, (sp - 72#64) ↦₃₂ t3) ∗
      (∃∗ t4 : BitVec 64, (sp - 68#64) ↦₆₄ t4) ∗
      (∃∗ t5 : BitVec 32, (sp - 60#64) ↦₃₂ t5) := by
  rw [ProofLib.memRegion_split' (b := sp - 88#64) (n := 8) (k := 24)
        (b' := sp - 80#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 4) (k := 20)
        (b' := sp - 76#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 76#64) (n := 4) (k := 16)
        (b' := sp - 72#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 4) (k := 12)
        (b' := sp - 68#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 68#64) (n := 8) (k := 4)
        (b' := sp - 60#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp - 88#64), memRegion_four (sp - 80#64),
      memRegion_four (sp - 76#64), memRegion_four (sp - 72#64),
      memRegion_eight (sp - 68#64), memRegion_four (sp - 60#64)]

theorem memRegion_sp88_32_for_simple (sp : BitVec 64) :
    memRegion (sp - 88#64) 32 =
      memRegion (sp - 88#64) 17 ∗ memRegion (sp - 71#64) 15 :=
  ProofLib.memRegion_split' (b := sp - 88#64) (n := 17) (k := 15)
    (b' := sp - 71#64) rfl (by bv_arith) (by decide)

theorem memRegion_sp52_17_none (sp : BitVec 64) :
    memRegion (sp - 52#64) 17 =
      (∃∗ b : BitVec 8, (sp - 52#64) ↦₈ b) ∗ memRegion (sp - 51#64) 16 := by
  rw [ProofLib.memRegion_split' (b := sp - 52#64) (n := 1) (k := 16)
        (b' := sp - 51#64) rfl (by bv_arith) (by decide),
      memRegion_one (sp - 52#64)]

theorem memRegion_sp52_17_some (sp : BitVec 64) :
    memRegion (sp - 52#64) 17 =
      (∃∗ b : BitVec 8, (sp - 52#64) ↦₈ b) ∗
      (∃∗ w0 : BitVec 64, (sp - 51#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (sp - 43#64) ↦₆₄ w1) := by
  rw [memRegion_sp52_17_none sp,
      ProofLib.memRegion_split' (b := sp - 51#64) (n := 8) (k := 8)
        (b' := sp - 43#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp - 51#64), memRegion_eight (sp - 43#64)]

theorem memRegion_sp88_17_none (sp : BitVec 64) :
    memRegion (sp - 88#64) 17 =
      (∃∗ b : BitVec 8, (sp - 88#64) ↦₈ b) ∗ memRegion (sp - 87#64) 16 := by
  rw [ProofLib.memRegion_split' (b := sp - 88#64) (n := 1) (k := 16)
        (b' := sp - 87#64) rfl (by bv_arith) (by decide),
      memRegion_one (sp - 88#64)]

theorem memRegion_sp88_17_some (sp : BitVec 64) :
    memRegion (sp - 88#64) 17 =
      (∃∗ b : BitVec 8, (sp - 88#64) ↦₈ b) ∗
      (∃∗ w0 : BitVec 64, (sp - 87#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (sp - 79#64) ↦₆₄ w1) := by
  rw [memRegion_sp88_17_none sp,
      ProofLib.memRegion_split' (b := sp - 87#64) (n := 8) (k := 8)
        (b' := sp - 79#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp - 87#64), memRegion_eight (sp - 79#64)]

theorem decodeHex32ResultAt_sp52_none (sp : BitVec 64) :
    decodeHex32ResultAt (sp - 52#64) none =
      ((sp - 52#64) ↦₈ 0#8) ∗ memRegion (sp - 51#64) 16 := by
  simp only [decodeHex32ResultAt]
  have h51 : sp - 52#64 + 1#64 = sp - 51#64 := by bv_arith
  rw [h51]

theorem decodeHex32ResultAt_sp52_some (sp : BitVec 64) (u : List.Vector (BitVec 8) 16) :
    decodeHex32ResultAt (sp - 52#64) (some u) =
      ((sp - 52#64) ↦₈ 1#8) ∗
      ((sp - 51#64) ↦₆₄ uuidWord0 u) ∗
      ((sp - 43#64) ↦₆₄ uuidWord1 u) := by
  simp only [decodeHex32ResultAt]
  have h51 : sp - 52#64 + 1#64 = sp - 51#64 := by bv_arith
  have h43 : sp - 51#64 + 8#64 = sp - 43#64 := by bv_arith
  rw [h51, pointsToBytes_uuid (sp - 51#64) u, h43]

theorem decodeHex32ResultAt_sp88_none (sp : BitVec 64) :
    decodeHex32ResultAt (sp - 88#64) none =
      ((sp - 88#64) ↦₈ 0#8) ∗ memRegion (sp - 87#64) 16 := by
  simp only [decodeHex32ResultAt]
  have h87 : sp - 88#64 + 1#64 = sp - 87#64 := by bv_arith
  rw [h87]

theorem decodeHex32ResultAt_sp88_some (sp : BitVec 64) (u : List.Vector (BitVec 8) 16) :
    decodeHex32ResultAt (sp - 88#64) (some u) =
      ((sp - 88#64) ↦₈ 1#8) ∗
      ((sp - 87#64) ↦₆₄ uuidWord0 u) ∗
      ((sp - 79#64) ↦₆₄ uuidWord1 u) := by
  simp only [decodeHex32ResultAt]
  have h87 : sp - 88#64 + 1#64 = sp - 87#64 := by bv_arith
  have h79 : sp - 87#64 + 8#64 = sp - 79#64 := by bv_arith
  rw [h87, pointsToBytes_uuid (sp - 87#64) u, h79]

/-! ## Execution lemmas for `uuid::parser::try_parse` (`0x4930c`) -/

abbrev parserPost (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (s0 : State)
    (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ parserTryParseSpec.post (p, bs, out17) s0 sf ∗ R) ∧
    sf.sp = s0.sp ∧
    CalleeSavedPreserved s0 sf

abbrev ParserRegsPreserved (s0 s : State) : Prop :=
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem wp_err_494b0 (b : BitVec 64)
    (hooks : String → Option (State → State))
    (entry : BitVec 64)
    (hentry : (libsignalSessionCode.rebase b
      hooks).fnAddr "uuid::parser::try_parse" = entry)
    (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8)
    (s0 s : State)
    (hsp_align : s0.spAligned = true)
    (huuid : uuidTryParse bs = none)
    (hpc : s.pc = entry + bv% (420))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (hx8 : s.readReg64 .x8 = out17)
    (htr : s.trace = s0.trace)
    (hcs : ParserRegsPreserved s0 s) :
    SepWP (libsignalSessionCode.rebase b hooks)
      (s0.readReg64 .x30) s
      (((p ↦ₛ bs) ∗
        (out17 ↦₆₄ out_w0) ∗ ((out17 + 8#64) ↦₆₄ out_w1) ∗ ((out17 + 16#64) ↦₈ out_b2)) ∗
       (stackAt (s0.sp - 96#64) 0x20 ∗
        memRegion (s0.sp - 96#64) 8 ∗
        memRegion (s0.sp - 88#64) 32 ∗
        memRegion (s0.sp - 56#64) 4 ∗
        memRegion (s0.sp - 52#64) 17 ∗
        memRegion (s0.sp - 35#64) 3 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (parserPost p bs out17 s0 R) := by
  subst entry
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  code_fetches libsignalSessionCode parserTryParseBin b
    hooks
    (ls_lemma% fnOff "uuid::parser::try_parse") (num% (ls_off% "uuid::parser::try_parse")) 536
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "uuid::parser::try_parse" = entry
  examples_hide_fetches
  wp_steps
  unfold parserPost parserTryParseSpec
  simp only [huuid, parserTryParseResultAt, stackAt_parser_split s0.sp]
  wp_done

theorem wp_simple_49454 (b : BitVec 64)
    (hooks : String → Option (State → State))
    (entry : BitVec 64)
    (hentry : (libsignalSessionCode.rebase b
      hooks).fnAddr "uuid::parser::try_parse" = entry)
    (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8)
    (s0 s : State)
    (hsp_align : s0.spAligned = true)
    (hlen : bs.length = 32)
    (hpc : s.pc = entry + bv% (328))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = p)
    (hx8 : s.readReg64 .x8 = out17)
    (htr : s.trace = s0.trace)
    (hcs : ParserRegsPreserved s0 s) :
    SepWP (libsignalSessionCode.rebase b hooks)
      (s0.readReg64 .x30) s
      (((p ↦ₛ bs) ∗
        (out17 ↦₆₄ out_w0) ∗ ((out17 + 8#64) ↦₆₄ out_w1) ∗ ((out17 + 16#64) ↦₈ out_b2)) ∗
       (stackAt (s0.sp - 96#64) 0x20 ∗
        memRegion (s0.sp - 96#64) 8 ∗
        memRegion (s0.sp - 88#64) 32 ∗
        memRegion (s0.sp - 56#64) 4 ∗
        memRegion (s0.sp - 52#64) 17 ∗
        memRegion (s0.sp - 35#64) 3 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (parserPost p bs out17 s0 R) := by
  subst entry
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have hcallee_hex := decodeHex32_ok_from_parser b hooks
  code_fetches libsignalSessionCode parserTryParseBin b
    hooks
    (ls_lemma% fnOff "uuid::parser::try_parse") (num% (ls_off% "uuid::parser::try_parse")) 536
  dsimp only [parserTryParseName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "uuid::parser::try_parse" = entry
  examples_hide_fetches
  have huuid : uuidTryParse bs = decodeHex32 bs := by
    unfold uuidTryParse parseSimple
    simp [hlen]
  rw [memRegion_sp88_32_for_simple s0.sp]
  wp_steps
  wp_apply
  cases hdec : decodeHex32 bs with
  | none =>
    rw [decodeHex32ResultAt_sp88_none s0.sp, hsp]
    wp_steps
    unfold parserPost parserTryParseSpec
    simp only [huuid, hdec, parserTryParseResultAt, stackAt_parser_split s0.sp,
      memRegion_sp88_32_for_simple s0.sp, memRegion_sp88_17_none s0.sp]
    wp_done
  | some u =>
    rw [decodeHex32ResultAt_sp88_some s0.sp u, hsp]
    wp_steps
    unfold parserPost parserTryParseSpec
    simp only [huuid, hdec, parserTryParseResultAt_some_eq, stackAt_parser_split s0.sp,
      memRegion_sp88_32_for_simple s0.sp, memRegion_sp88_17_some s0.sp]
    wp_done

set_option maxHeartbeats 800000 in
theorem wp_hyphenated_49338 (b : BitVec 64)
    (hooks : String → Option (State → State))
    (entry : BitVec 64)
    (hentry : (libsignalSessionCode.rebase b
      hooks).fnAddr "uuid::parser::try_parse" = entry)
    (p p19 : BitVec 64) (bs s36 : List (BitVec 8)) (Frame : SepProp) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8)
    (s0 s : State)
    (hsp_align : s0.spAligned = true)
    (hs36 : s36.length = 36)
    (hframe : (p ↦ₛ bs) = ((p19 ↦ₛ s36) ∗ Frame))
    (huuid : uuidTryParse bs = parseHyphenated s36)
    (hpc : s.pc = entry + bv% (44))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = p19)
    (hx8 : s.readReg64 .x8 = out17)
    (hx29 : s.readReg64 .x29 = s0.sp - 32#64)
    (htr : s.trace = s0.trace)
    (hcs : ParserRegsPreserved s0 s) :
    SepWP (libsignalSessionCode.rebase b hooks)
      (s0.readReg64 .x30) s
      ((((p19 ↦ₛ s36) ∗ Frame) ∗
        (out17 ↦₆₄ out_w0) ∗ ((out17 + 8#64) ↦₆₄ out_w1) ∗ ((out17 + 16#64) ↦₈ out_b2)) ∗
       (stackAt (s0.sp - 96#64) 0x20 ∗
        memRegion (s0.sp - 96#64) 8 ∗
        memRegion (s0.sp - 88#64) 32 ∗
        memRegion (s0.sp - 56#64) 4 ∗
        memRegion (s0.sp - 52#64) 17 ∗
        memRegion (s0.sp - 35#64) 3 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (parserPost p bs out17 s0 R) := by
  subst entry
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have hcallee_hex := decodeHex32_ok_from_parser b hooks
  code_fetches libsignalSessionCode parserTryParseBin b
    hooks
    (ls_lemma% fnOff "uuid::parser::try_parse") (num% (ls_off% "uuid::parser::try_parse")) 536
  dsimp only [parserTryParseName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "uuid::parser::try_parse" = entry
  examples_hide_fetches
  rcases exists_36_parts s36 hs36 with
    ⟨hex32, b8, b13, b18, b23, w0, w4, w1, w2, w3, w5,
     hhex_len, hb8, hb13, hb18, hb23, hhex_eq, hp19_split, hsp_hex32⟩
  have hph := parseHyphenated_of_parts s36 hex32 b8 b13 b18 b23 hs36 hb8 hb13 hb18 hb23 hhex_eq
  rw [hp19_split p19, memRegion_sp88_32_for_hyphen s0.sp]
  wp_pull_exists
  wp_steps
  wp_if h8
  · wp_steps
    have hnone := parseHyphenated_ne_8 hph h8
    unfold parserPost parserTryParseSpec
    simp only [hframe, hp19_split p19, huuid, hnone, parserTryParseResultAt,
      stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]
    wp_done
  · wp_steps
    wp_if h13
    · wp_steps
      have hnone := parseHyphenated_ne_13 hph h13
      unfold parserPost parserTryParseSpec
      simp only [hframe, hp19_split p19, huuid, hnone, parserTryParseResultAt,
        stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]
      wp_done
    · wp_steps
      wp_if h18
      · wp_steps
        have hnone := parseHyphenated_ne_18 hph h18
        unfold parserPost parserTryParseSpec
        simp only [hframe, hp19_split p19, huuid, hnone, parserTryParseResultAt,
          stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]
        wp_done
      · wp_steps
        wp_if h23
        · wp_steps
          have hnone := parseHyphenated_ne_23 hph h23
          unfold parserPost parserTryParseSpec
          simp only [hframe, hp19_split p19, huuid, hnone, parserTryParseResultAt,
            stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]
          wp_done
        · wp_steps
          have hall := parseHyphenated_all_eq hph h8 h13 h18 h23
          apply SepWP.focus_rw (hsp_hex32 s0.sp)
          wp_apply
          cases hdec : decodeHex32 hex32 with
          | none =>
            rw [decodeHex32ResultAt_sp52_none s0.sp, ← hsp_hex32 s0.sp, hsp]
            wp_steps
            unfold parserPost parserTryParseSpec
            simp only [hframe, hp19_split p19, huuid, hall, hdec, parserTryParseResultAt,
              stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp,
              memRegion_sp52_17_none s0.sp]
            wp_done
          | some u =>
            rw [decodeHex32ResultAt_sp52_some s0.sp u, ← hsp_hex32 s0.sp, hsp]
            wp_steps
            unfold parserPost parserTryParseSpec
            simp only [hframe, hp19_split p19, huuid, hall, hdec, parserTryParseResultAt_some_eq,
              stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp,
              memRegion_sp52_17_some s0.sp]
            wp_done

end CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse
