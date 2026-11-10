/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.ParserHyphenated
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Verification of `uuid::parser::try_parse` and `<uuid::Uuid>::try_parse`

Verifies the 38-byte braced and 45-byte URN branches of `uuid::parser::try_parse`, assembles
`parserTryParse_ok`, and proves `uuidTryParse_ok_impl` for `<uuid::Uuid>::try_parse`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
  CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## BitVec / List length helpers for entry dispatch -/

theorem eq_ofNat_of_toNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) :
    x = BitVec.ofNat 64 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem len_eq_of_reg_eq {x : BitVec 64} {n k : Nat}
    (hx : x.toNat = n) (h : x = BitVec.ofNat 64 k) (hk : k < 2 ^ 64 := by decide) :
    n = k := by
  have := congrArg BitVec.toNat h
  rw [hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
  exact this

theorem len_ne_of_reg_ne {x : BitVec 64} {n k : Nat}
    (hx : x.toNat = n) (h : x ≠ BitVec.ofNat 64 k) :
    n ≠ k := by
  intro hn
  apply h
  rw [eq_ofNat_of_toNat_eq hx, hn]

theorem uuidTryParse_of_other_len {bs : List (BitVec 8)}
    (h32 : bs.length ≠ 32) (h36 : bs.length ≠ 36)
    (h38 : bs.length ≠ 38) (h45 : bs.length ≠ 45) :
    uuidTryParse bs = none := by
  unfold uuidTryParse
  simp [h32, h36, h38, h45]

/-! ## Pure decomposition of 38-byte braced inputs -/

theorem exists_38_parts (bs : List (BitVec 8)) (h : bs.length = 38) :
    ∃ (b0 b37 : BitVec 8) (s36 : List (BitVec 8)),
      s36.length = 36 ∧
      bs = [b0] ++ (s36 ++ [b37]) ∧
      uuidTryParse bs =
        (if b0 = 0x7b#8 ∧ b37 = 0x7d#8 then parseHyphenated s36 else none) ∧
      (∀ p : BitVec 64,
        (p ↦ₛ bs) =
          ((p + 1#64) ↦ₛ s36) ∗ ((p ↦₈ b0) ∗ ((p + 37#64) ↦₈ b37))) := by
  let b0 := bs[0]'(by omega)
  let s36 := (bs.drop 1).take 36
  let b37 := bs[37]'(by omega)
  have hs36 : s36.length = 36 := by simp [s36, h]
  have hbs0 : bs = [b0] ++ bs.drop 1 := by
    conv => lhs; rw [← List.take_append_drop 1 bs]
    rw [List.take_one, List.head?_eq_getElem?, getElem?_pos bs 0 (by omega), Option.toList_some]
  have hbs1 : bs.drop 1 = s36 ++ [b37] := by
    have := drop_eq_take_append_cons_drop bs 1 36 (by omega)
    have h38 : bs.drop 38 = [] := List.drop_eq_nil_of_le (by omega)
    rw [h38, List.append_nil] at this
    exact this
  have hbs : bs = [b0] ++ (s36 ++ [b37]) := by rw [hbs0, hbs1]
  have hhead : bs.head? = some b0 := by simp [hbs]
  have hlast : bs.getLast? = some b37 := by
    have : bs = ([b0] ++ s36) ++ [b37] := by simp [hbs]
    rw [this, List.getLast?_concat]
  have hdrop : bs.tail.take 36 = s36 := by rw [hbs0]; rfl
  have huuid : uuidTryParse bs =
      (if b0 = 0x7b#8 ∧ b37 = 0x7d#8 then parseHyphenated s36 else none) := by
    unfold uuidTryParse
    simp [h, hhead, hlast, hdrop]
  refine ⟨b0, b37, s36, hs36, hbs, huuid, fun p => ?_⟩
  have h1 := pointsToBytes_append p [b0] (s36 ++ [b37])
  have h2 := pointsToBytes_append (p + 1#64) s36 [b37]
  have hlen36 : BitVec.ofNat 64 s36.length = 36#64 := by rw [hs36]
  have hp37 : p + 1#64 + 36#64 = p + 37#64 := by bv_arith
  rw [hbs, h1, pointsToBytes_singleton p b0]
  change (p ↦₈ b0) ∗ ((p + 1#64) ↦ₛ (s36 ++ [b37])) = _
  rw [h2, hlen36, hp37, pointsToBytes_singleton (p + 37#64) b37]
  simp only [sepConj_left_comm]

theorem braced_ne_0 {bs s36 : List (BitVec 8)} {b0 b37 : BitVec 8}
    (hu : uuidTryParse bs = if b0 = 0x7b#8 ∧ b37 = 0x7d#8 then parseHyphenated s36 else none)
    (hne : BitVec.zeroExtend 32 b0 ≠ 123#32) :
    uuidTryParse bs = none := by
  have : b0 ≠ 0x7b#8 := fun h => hne (by subst h; rfl)
  simp [hu, this]

theorem braced_ne_37 {bs s36 : List (BitVec 8)} {b0 b37 : BitVec 8}
    (hu : uuidTryParse bs = if b0 = 0x7b#8 ∧ b37 = 0x7d#8 then parseHyphenated s36 else none)
    (hne : BitVec.zeroExtend 32 b37 ≠ 125#32) :
    uuidTryParse bs = none := by
  have : b37 ≠ 0x7d#8 := fun h => hne (by subst h; rfl)
  simp [hu, this]

theorem braced_all_eq {bs s36 : List (BitVec 8)} {b0 b37 : BitVec 8}
    (hu : uuidTryParse bs = if b0 = 0x7b#8 ∧ b37 = 0x7d#8 then parseHyphenated s36 else none)
    (h0 : BitVec.zeroExtend 64 b0 = 123#64)
    (h37 : BitVec.zeroExtend 64 b37 = 125#64) :
    uuidTryParse bs = parseHyphenated s36 := by
  have e0 : b0 = 0x7b#8 := byte_eq_of_zext64_eq h0
  have e37 : b37 = 0x7d#8 := byte_eq_of_zext64_eq h37
  simp [hu, e0, e37]

/-! ## Pure decomposition of 45-byte URN inputs -/

theorem urnPrefix_val :
    urnPrefix = [0x75#8, 0x72#8, 0x6e#8, 0x3a#8, 0x75#8, 0x75#8, 0x69#8, 0x64#8, 0x3a#8] := by
  decide +kernel

theorem exists_word9_of_length_9 (s : List (BitVec 8)) (h : s.length = 9) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8,
      s = [b0, b1, b2, b3, b4, b5, b6, b7, b8] := by
  rcases s with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at h)
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩

theorem pointsToBytes9_eq (p : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) :
    (p ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8]) =
      (p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦₈ b2) ∗ ((p + 3#64) ↦₈ b3) ∗
      ((p + 4#64) ↦₈ b4) ∗ ((p + 5#64) ↦₈ b5) ∗ ((p + 6#64) ↦₈ b6) ∗
      ((p + 7#64) ↦₈ b7) ∗ ((p + 8#64) ↦₈ b8) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem exists_45_parts (bs : List (BitVec 8)) (h : bs.length = 45) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) (s36 : List (BitVec 8)),
      s36.length = 36 ∧
      uuidTryParse bs =
        (if 0x75#8 = b0 ∧ 0x72#8 = b1 ∧ 0x6e#8 = b2 ∧ 0x3a#8 = b3 ∧
            0x75#8 = b4 ∧ 0x75#8 = b5 ∧ 0x69#8 = b6 ∧ 0x64#8 = b7 ∧ 0x3a#8 = b8
         then parseHyphenated s36 else none) ∧
      (∀ p : BitVec 64,
        (p ↦ₛ bs) =
          ((p + 9#64) ↦ₛ s36) ∗
          ((p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦₈ b2) ∗ ((p + 3#64) ↦₈ b3) ∗
           ((p + 4#64) ↦₈ b4) ∗ ((p + 5#64) ↦₈ b5) ∗ ((p + 6#64) ↦₈ b6) ∗
           ((p + 7#64) ↦₈ b7) ∗ ((p + 8#64) ↦₈ b8))) := by
  let pfx := bs.take 9
  let s36 := bs.drop 9
  have hpfx_len : pfx.length = 9 := by simp [pfx, h]
  have hs36_len : s36.length = 36 := by simp [s36, h]
  rcases exists_word9_of_length_9 pfx hpfx_len with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, hpfx⟩
  have hbs : bs = [b0, b1, b2, b3, b4, b5, b6, b7, b8] ++ s36 := by
    rw [← hpfx]
    exact (List.take_append_drop 9 bs).symm
  have huuid : uuidTryParse bs =
      (if 0x75#8 = b0 ∧ 0x72#8 = b1 ∧ 0x6e#8 = b2 ∧ 0x3a#8 = b3 ∧
          0x75#8 = b4 ∧ 0x75#8 = b5 ∧ 0x69#8 = b6 ∧ 0x64#8 = b7 ∧ 0x3a#8 = b8
       then parseHyphenated s36 else none) := by
    unfold uuidTryParse
    rw [urnPrefix_val]
    simp [hbs, hs36_len, List.isPrefixOf]
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, s36, hs36_len, huuid, fun p => ?_⟩
  have h1 := pointsToBytes_append p [b0, b1, b2, b3, b4, b5, b6, b7, b8] s36
  have hlen9 : BitVec.ofNat 64 [b0, b1, b2, b3, b4, b5, b6, b7, b8].length = 9#64 := rfl
  rw [hbs, h1, hlen9, pointsToBytes9_eq p b0 b1 b2 b3 b4 b5 b6 b7 b8, sepConj_comm]

theorem urn_all_eq {bs s36 : List (BitVec 8)} {b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8}
    (hu : uuidTryParse bs =
      if 0x75#8 = b0 ∧ 0x72#8 = b1 ∧ 0x6e#8 = b2 ∧ 0x3a#8 = b3 ∧
         0x75#8 = b4 ∧ 0x75#8 = b5 ∧ 0x69#8 = b6 ∧ 0x64#8 = b7 ∧ 0x3a#8 = b8
      then parseHyphenated s36 else none)
    (h0 : BitVec.zeroExtend 64 b0 = 117#64)
    (h1 : BitVec.zeroExtend 64 b1 = 114#64)
    (h2 : BitVec.zeroExtend 64 b2 = 110#64)
    (h3 : BitVec.zeroExtend 64 b3 = 58#64)
    (h4 : BitVec.zeroExtend 64 b4 = 117#64)
    (h5 : BitVec.zeroExtend 64 b5 = 117#64)
    (h6 : BitVec.zeroExtend 64 b6 = 105#64)
    (h7 : BitVec.zeroExtend 64 b7 = 100#64)
    (h8 : BitVec.zeroExtend 64 b8 = 58#64) :
    uuidTryParse bs = parseHyphenated s36 := by
  have e0 : b0 = 0x75#8 := byte_eq_of_zext64_eq h0
  have e1 : b1 = 0x72#8 := byte_eq_of_zext64_eq h1
  have e2 : b2 = 0x6e#8 := byte_eq_of_zext64_eq h2
  have e3 : b3 = 0x3a#8 := byte_eq_of_zext64_eq h3
  have e4 : b4 = 0x75#8 := byte_eq_of_zext64_eq h4
  have e5 : b5 = 0x75#8 := byte_eq_of_zext64_eq h5
  have e6 : b6 = 0x69#8 := byte_eq_of_zext64_eq h6
  have e7 : b7 = 0x64#8 := byte_eq_of_zext64_eq h7
  have e8 : b8 = 0x3a#8 := byte_eq_of_zext64_eq h8
  subst e0 e1 e2 e3 e4 e5 e6 e7 e8
  simp [hu]

/-! ## Symbolic execution of braced (`0x49490`) and URN (`0x493e0`) branches -/

set_option maxHeartbeats 800000 in
theorem wp_braced_49490 (b : BitVec 64)
    (hooks : String → Option (State → State))
    (entry : BitVec 64)
    (hentry : (libsignalSessionCode.rebase b
      hooks).fnAddr "uuid::parser::try_parse" = entry)
    (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8)
    (s0 s : State)
    (hsp_align : s0.spAligned = true)
    (hlen : bs.length = 38)
    (hpc : s.pc = entry + bv% (388))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = p)
    (hx8 : s.readReg64 .x8 = out17)
    (hx29 : s.readReg64 .x29 = s0.sp - 32#64)
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
  have h_hyph := wp_hyphenated_49338 b hooks _ rfl
  code_fetches libsignalSessionCode parserTryParseBin b
    hooks
    (ls_lemma% fnOff "uuid::parser::try_parse") (num% (ls_off% "uuid::parser::try_parse")) 536
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "uuid::parser::try_parse" = entry
  examples_hide_fetches
  rcases exists_38_parts bs hlen with ⟨b0, b37, s36, hs36, _, huuid, hp_split⟩
  rw [hp_split p]
  wp_steps
  wp_if hb0
  · wp_steps
    have hnone := braced_ne_0 huuid hb0
    unfold parserPost parserTryParseSpec
    simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
    wp_done
  · wp_steps
    wp_if hb37
    · wp_steps
      have hnone := braced_ne_37 huuid hb37
      unfold parserPost parserTryParseSpec
      simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
      wp_done
    · wp_step
      wp_step
      have hall := braced_all_eq huuid hb0 hb37
      exact h_hyph p (p + 1#64) bs s36
        ((p ↦₈ b0) ∗ ((p + 37#64) ↦₈ b37)) out17 R out_w0 out_w1 out_b2 s0 _
        hsp_align hs36 (hp_split p) hall
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs)
        ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
         by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩

set_option maxHeartbeats 1600000 in
theorem wp_urn_493e0 (b : BitVec 64)
    (hooks : String → Option (State → State))
    (entry : BitVec 64)
    (hentry : (libsignalSessionCode.rebase b
      hooks).fnAddr "uuid::parser::try_parse" = entry)
    (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8)
    (s0 s : State)
    (hsp_align : s0.spAligned = true)
    (hlen : bs.length = 45)
    (hpc : s.pc = entry + bv% (212))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = p)
    (hx8 : s.readReg64 .x8 = out17)
    (hx29 : s.readReg64 .x29 = s0.sp - 32#64)
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
  have h_hyph := wp_hyphenated_49338 b hooks _ rfl
  code_fetches libsignalSessionCode parserTryParseBin b
    hooks
    (ls_lemma% fnOff "uuid::parser::try_parse") (num% (ls_off% "uuid::parser::try_parse")) 536
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "uuid::parser::try_parse" = entry
  examples_hide_fetches
  rcases exists_45_parts bs hlen with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, s36, hs36, huuid, hp_split⟩
  rw [hp_split p]
  wp_steps
  wp_if hb0
  · wp_steps
    have hnone : uuidTryParse bs = none := by
      have : 0x75#8 ≠ b0 := fun h => hb0 (by subst h; rfl)
      simp [huuid, this]
    unfold parserPost parserTryParseSpec
    simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
    wp_done
  · wp_steps
    wp_if hb1
    · wp_steps
      have hnone : uuidTryParse bs = none := by
        have : 0x72#8 ≠ b1 := fun h => hb1 (by subst h; rfl)
        simp [huuid, this]
      unfold parserPost parserTryParseSpec
      simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
      wp_done
    · wp_steps
      wp_if hb2
      · wp_steps
        have hnone : uuidTryParse bs = none := by
          have : 0x6e#8 ≠ b2 := fun h => hb2 (by subst h; rfl)
          simp [huuid, this]
        unfold parserPost parserTryParseSpec
        simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
        wp_done
      · wp_steps
        wp_if hb3
        · wp_steps
          have hnone : uuidTryParse bs = none := by
            have : 0x3a#8 ≠ b3 := fun h => hb3 (by subst h; rfl)
            simp [huuid, this]
          unfold parserPost parserTryParseSpec
          simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
          wp_done
        · wp_steps
          wp_if hb4
          · wp_steps
            have hnone : uuidTryParse bs = none := by
              have : 0x75#8 ≠ b4 := fun h => hb4 (by subst h; rfl)
              simp [huuid, this]
            unfold parserPost parserTryParseSpec
            simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
            wp_done
          · wp_steps
            wp_if hb5
            · wp_steps
              have hnone : uuidTryParse bs = none := by
                have : 0x75#8 ≠ b5 := fun h => hb5 (by subst h; rfl)
                simp [huuid, this]
              unfold parserPost parserTryParseSpec
              simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
              wp_done
            · wp_steps
              wp_if hb6
              · wp_steps
                have hnone : uuidTryParse bs = none := by
                  have : 0x69#8 ≠ b6 := fun h => hb6 (by subst h; rfl)
                  simp [huuid, this]
                unfold parserPost parserTryParseSpec
                simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
                wp_done
              · wp_steps
                wp_if hb7
                · wp_steps
                  have hnone : uuidTryParse bs = none := by
                    have : 0x64#8 ≠ b7 := fun h => hb7 (by subst h; rfl)
                    simp [huuid, this]
                  unfold parserPost parserTryParseSpec
                  simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
                  wp_done
                · wp_steps
                  wp_if hb8
                  · wp_steps
                    have hnone : uuidTryParse bs = none := by
                      have : 0x3a#8 ≠ b8 := fun h => hb8 (by subst h; rfl)
                      simp [huuid, this]
                    unfold parserPost parserTryParseSpec
                    simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
                    wp_done
                  · wp_step
                    wp_step
                    have hall := urn_all_eq huuid hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
                    exact h_hyph p (p + 9#64) bs s36
                      ((p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦₈ b2) ∗
                       ((p + 3#64) ↦₈ b3) ∗ ((p + 4#64) ↦₈ b4) ∗ ((p + 5#64) ↦₈ b5) ∗
                       ((p + 6#64) ↦₈ b6) ∗ ((p + 7#64) ↦₈ b7) ∗ ((p + 8#64) ↦₈ b8))
                      out17 R out_w0 out_w1 out_b2 s0 _
                      hsp_align hs36 (hp_split p) hall
                      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
                      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
                      (by wp_norm_lhs)
                      ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
                       by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩

/-! ## `parserTryParse_ok` (`0x4930c`) -/

theorem subroutine_ok_of_sepWP_simple {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry_pc →
      s0.status = .Running →
      s0.spAligned = true →
      SepWP prog (s0.readReg64 (Reg.gpr 30#5)) s0 (spec.pre x s0)
        (fun sf Q =>
          (sf.mem ⊨ Q ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf)) :
    subroutine_ok prog entry_pc spec := by
  apply subroutine_ok_of_sepWP
  intro x R s0 hpc hrun hpre hsp_align
  exact ⟨spec.pre x s0, R, hpre, h x R s0 hpc hrun hsp_align⟩

theorem sepWP_parser_branch {prog : Program} {target_pc : BitVec 64} {s : State}
    {P1 P2 P3 P4 Rest : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s ((P1 ∗ P2 ∗ P3 ∗ P4) ∗ Rest) post) :
    SepWP prog target_pc s (P1 ∗ P2 ∗ P3 ∗ P4 ∗ Rest) post := by
  simpa only [sepConj_assoc] using h

theorem sepWP_parser_hyph36 {prog : Program} {target_pc : BitVec 64} {s : State}
    {P1 P2 P3 P4 Rest : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s (((P1 ∗ emp) ∗ P2 ∗ P3 ∗ P4) ∗ Rest) post) :
    SepWP prog target_pc s (P1 ∗ P2 ∗ P3 ∗ P4 ∗ Rest) post := by
  simpa only [sepConj_assoc, emp_sepConj] using h

set_option maxHeartbeats 800000 in
theorem parserTryParse_ok (b : BitVec 64)
    (hooks : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr parserTryParseName)
      parserTryParseSpec := by
  apply subroutine_ok_of_sepWP_simple
  intro ⟨p, bs, out17⟩ R s0 hpc hrun hsp
  change SepWP (libsignalSessionCode.rebase b hooks) (s0.readReg64 .x30) s0
    ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧ s0.readReg64 .x8 = out17⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out17 17) ∗ stackAt s0.sp 0x80)
    (parserPost p bs out17 s0 R)
  have h_braced := wp_braced_49490 b hooks _ rfl
  have h_urn := wp_urn_493e0 b hooks _ rfl
  have h_simple := wp_simple_49454 b hooks _ rfl
  have h_hyph := wp_hyphenated_49338 b hooks _ rfl
  have h_err := wp_err_494b0 b hooks _ rfl
  code_fetches libsignalSessionCode parserTryParseBin b
    hooks
    (ls_lemma% fnOff "uuid::parser::try_parse") (num% (ls_off% "uuid::parser::try_parse")) 536
  dsimp only [parserTryParseName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "uuid::parser::try_parse" = entry
  examples_hide_fetches
  simp only [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hx0, hx1, hx8⟩
  rw [memRegion_out17_split out17, stackAt_parser_split s0.sp]
  wp_pull_exists
  wp_steps
  wp_if hgt
  · -- Branch `0x493d0`: `x1 >s 37`
    have hne32 : bs.length ≠ 32 := by
      intro hlen
      have hx : s0.readReg64 .x1 = 32#64 := by rw [eq_ofNat_of_toNat_eq hx1, hlen]
      rw [hx] at hgt
      revert hgt; decide
    have hne36 : bs.length ≠ 36 := by
      intro hlen
      have hx : s0.readReg64 .x1 = 36#64 := by rw [eq_ofNat_of_toNat_eq hx1, hlen]
      rw [hx] at hgt
      revert hgt; decide
    wp_steps
    wp_if heq38
    · -- `x1 = 38` -> `0x49490`
      have hlen38 : bs.length = 38 := len_eq_of_reg_eq hx1 heq38
      apply sepWP_parser_branch
      refine h_braced p bs out17 R _ _ _ s0 _
        hsp hlen38 ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
    · have hne38 : bs.length ≠ 38 := len_ne_of_reg_ne hx1 heq38
      wp_steps
      wp_if hne45_reg
      · -- `x1 ≠ 45` -> `0x494b0`
        have hne45 : bs.length ≠ 45 := len_ne_of_reg_ne hx1 hne45_reg
        have huuid := uuidTryParse_of_other_len hne32 hne36 hne38 hne45
        apply sepWP_parser_branch
        refine h_err p bs out17 R _ _ _ s0 _
          hsp huuid ?_ ?_ ?_ ?_ ?_
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
      · -- `x1 = 45` -> `0x493e0`
        have hlen45 : bs.length = 45 := len_eq_of_reg_eq hx1 hne45_reg
        apply sepWP_parser_branch
        refine h_urn p bs out17 R _ _ _ s0 _
          hsp hlen45 ?_ ?_ ?_ ?_ ?_ ?_ ?_
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
  · -- Fallthrough `0x49328`: `¬ (x1 >s 37)`
    have hne38 : bs.length ≠ 38 := by
      intro hlen
      have hx : s0.readReg64 .x1 = 38#64 := by rw [eq_ofNat_of_toNat_eq hx1, hlen]
      rw [hx] at hgt
      revert hgt; decide
    have hne45 : bs.length ≠ 45 := by
      intro hlen
      have hx : s0.readReg64 .x1 = 45#64 := by rw [eq_ofNat_of_toNat_eq hx1, hlen]
      rw [hx] at hgt
      revert hgt; decide
    wp_steps
    wp_if heq32
    · -- `x1 = 32` -> `0x49454`
      have hlen32 : bs.length = 32 := len_eq_of_reg_eq hx1 heq32
      apply sepWP_parser_branch
      refine h_simple p bs out17 R _ _ _ s0 _
        hsp hlen32 ?_ ?_ ?_ ?_ ?_ ?_
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
    · have hne32 : bs.length ≠ 32 := len_ne_of_reg_ne hx1 heq32
      wp_steps
      wp_if hne36_reg
      · -- `x1 ≠ 36` -> `0x494b0`
        have hne36 : bs.length ≠ 36 := len_ne_of_reg_ne hx1 hne36_reg
        have huuid := uuidTryParse_of_other_len hne32 hne36 hne38 hne45
        apply sepWP_parser_branch
        refine h_err p bs out17 R _ _ _ s0 _
          hsp huuid ?_ ?_ ?_ ?_ ?_
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
      · -- `x1 = 36` -> `0x49338`
        have hlen36 : bs.length = 36 := len_eq_of_reg_eq hx1 hne36_reg
        have huuid : uuidTryParse bs = parseHyphenated bs := by
          unfold uuidTryParse
          simp [hlen36]
        have hframe : (p ↦ₛ bs) = ((p ↦ₛ bs) ∗ emp) := (sepConj_emp (p ↦ₛ bs)).symm
        apply sepWP_parser_hyph36
        refine h_hyph p p bs bs emp out17 R _ _ _ s0 _
          hsp hlen36 hframe huuid ?_ ?_ ?_ ?_ ?_ ?_ ?_
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs

/-! ## `<uuid::Uuid>::try_parse` (`0x48a80`) -/

theorem parserTryParse_ok_from_uuid (b : BitVec 64)
    (hooks : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr uuidTryParseName + bv% (ls_off% "uuid::parser::try_parse" - ls_off% "<uuid::Uuid>::try_parse"))
      parserTryParseSpec := by
  have h : (libsignalSessionCode.rebase b hooks).fnAddr uuidTryParseName + bv% (ls_off% "uuid::parser::try_parse" - ls_off% "<uuid::Uuid>::try_parse") =
      (libsignalSessionCode.rebase b hooks).fnAddr parserTryParseName := by
    simp only [Program.fnAddr_rebase, uuidTryParseName, parserTryParseName,
      (ls_lemma% fnOff "<uuid::Uuid>::try_parse"), (ls_lemma% fnOff "uuid::parser::try_parse")]
    bv_arith
  rw [h]
  exact parserTryParse_ok b hooks

theorem memRegion_out32_split (out : BitVec 64) :
    memRegion out 32 =
      (∃∗ w_tag : BitVec 32, out ↦₃₂ w_tag) ∗
      (∃∗ w_u0 : BitVec 64, (out + 4#64) ↦₆₄ w_u0) ∗
      (∃∗ w_u1 : BitVec 64, (out + 12#64) ↦₆₄ w_u1) ∗
      memRegion (out + 20#64) 12 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 4) (k := 28)
        (b' := out + 4#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := out + 4#64) (n := 8) (k := 20)
        (b' := out + 12#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := out + 12#64) (n := 8) (k := 12)
        (b' := out + 20#64) rfl (by bv_arith) (by decide),
      memRegion_four out, memRegion_eight (out + 4#64), memRegion_eight (out + 12#64)]

theorem memRegion_out28_split (out : BitVec 64) :
    memRegion (out + 4#64) 28 =
      (∃∗ w_u0 : BitVec 64, (out + 4#64) ↦₆₄ w_u0) ∗
      (∃∗ w_u1 : BitVec 64, (out + 12#64) ↦₆₄ w_u1) ∗
      memRegion (out + 20#64) 12 := by
  rw [ProofLib.memRegion_split' (b := out + 4#64) (n := 8) (k := 20)
        (b' := out + 12#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := out + 12#64) (n := 8) (k := 12)
        (b' := out + 20#64) rfl (by bv_arith) (by decide),
      memRegion_eight (out + 4#64), memRegion_eight (out + 12#64)]

theorem stackAt_uuid_split (sp : BitVec 64) :
    stackAt sp uuidTryParseStack =
      stackAt (sp - 64#64) 0x80 ∗
      memRegion (sp - 64#64) 8 ∗
      memRegion (sp - 56#64) 17 ∗
      memRegion (sp - 39#64) 7 ∗
      (∃∗ s29 : BitVec 64, (sp - 32#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 24#64) ↦₆₄ s30) ∗
      (∃∗ s19 : BitVec 64, (sp - 16#64) ↦₆₄ s19) ∗
      memRegion (sp - 8#64) 8 := by
  simp only [stackAt, uuidTryParseStack]
  rw [ProofLib.memRegion_split' (b := sp - 192#64) (n := 128) (k := 64)
        (b' := sp - 64#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 56)
        (b' := sp - 56#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 17) (k := 39)
        (b' := sp - 39#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 39#64) (n := 7) (k := 32)
        (b' := sp - 32#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp - 32#64), memRegion_eight (sp - 24#64), memRegion_eight (sp - 16#64)]
  have h192 : sp - 64#64 - BitVec.ofNat 64 128 = sp - 192#64 := by bv_arith
  rw [h192]

theorem parserTryParseResultAt_sp56_none (sp : BitVec 64) :
    parserTryParseResultAt (sp - 56#64) none =
      (∃∗ w0 : BitVec 64, (sp - 56#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (sp - 48#64) ↦₆₄ w1) ∗
      (∃∗ tag : BitVec 8, ⌜tag ≠ 0xff#8⌝ ∗ ((sp - 40#64) ↦₈ tag)) := by
  simp only [parserTryParseResultAt]
  have h48 : sp - 56#64 + 8#64 = sp - 48#64 := by bv_arith
  have h40 : sp - 56#64 + 16#64 = sp - 40#64 := by bv_arith
  rw [h48, h40]

theorem parserTryParseResultAt_sp56_some (sp : BitVec 64) (u : List.Vector (BitVec 8) 16) :
    parserTryParseResultAt (sp - 56#64) (some u) =
      ((sp - 56#64) ↦₆₄ uuidWord0 u) ∗
      ((sp - 48#64) ↦₆₄ uuidWord1 u) ∗
      ((sp - 40#64) ↦₈ 0xff#8) := by
  rw [parserTryParseResultAt_some_eq]
  have h48 : sp - 56#64 + 8#64 = sp - 48#64 := by bv_arith
  have h40 : sp - 56#64 + 16#64 = sp - 40#64 := by bv_arith
  rw [h48, h40]

theorem memRegion_sp56_17_split (sp : BitVec 64) :
    memRegion (sp - 56#64) 17 =
      (∃∗ w0 : BitVec 64, (sp - 56#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (sp - 48#64) ↦₆₄ w1) ∗
      (∃∗ tag : BitVec 8, (sp - 40#64) ↦₈ tag) := by
  rw [memRegion_out17_split (sp - 56#64)]
  have h48 : sp - 56#64 + 8#64 = sp - 48#64 := by bv_arith
  have h40 : sp - 56#64 + 16#64 = sp - 40#64 := by bv_arith
  rw [h48, h40]

theorem uuidResultAt_some_eq (out : BitVec 64) (u : List.Vector (BitVec 8) 16) :
    uuidResultAt out (some u) =
      (out ↦₃₂ 0xffffffff#32) ∗
      ((out + 4#64) ↦₆₄ uuidWord0 u) ∗
      ((out + 12#64) ↦₆₄ uuidWord1 u) ∗
      memRegion (out + 20#64) 12 := by
  simp only [uuidResultAt, uuidOkTag, pointsToBytes_uuid (out + 4#64) u]
  have h12 : out + 4#64 + 8#64 = out + 12#64 := by bv_arith
  rw [h12]
  simp only [sepConj_assoc]

theorem uuidTryParse_ok_impl (b : BitVec 64)
    (hooks : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr uuidTryParseName)
      (uuidTryParseCodeSpec uuidTryParse) := by
  have hcallee := parserTryParse_ok_from_uuid b hooks
  apply subroutine_ok_of_sepWP_simple
  intro ⟨p, bs, out⟩ R s0 hpc hrun hsp
  code_fetches libsignalSessionCode uuidTryParseBin b
    hooks
    (ls_lemma% fnOff "<uuid::Uuid>::try_parse") (num% (ls_off% "<uuid::Uuid>::try_parse")) 96
  dsimp only [uuidTryParseName, uuidTryParseCodeSpec, uuidTryParseSpec,
    BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "<uuid::Uuid>::try_parse" = entry
  examples_hide_fetches
  simp only [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hx0, hx1, hx8⟩
  rw [memRegion_out32_split out, stackAt_uuid_split s0.sp]
  wp_pull_exists
  wp_steps
  wp_apply
  cases huuid : uuidTryParse bs with
  | none =>
    rw [parserTryParseResultAt_sp56_none s0.sp]
    wp_pull_exists
    wp_focus_pure; intro _htag
    wp_steps
    simp only [uuidResultAt, uuidErrParseOther, memRegion_out28_split out,
      memRegion_sp56_17_split s0.sp]
    wp_done
  | some u =>
    rw [parserTryParseResultAt_sp56_some s0.sp u]
    wp_steps
    simp only [uuidResultAt_some_eq out u, memRegion_sp56_17_split s0.sp]
    wp_done

end CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse
