/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.ParserHyphenated
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsDecodeHex32
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `.keepsFs` Path Lemmas for `uuid::parser::try_parse`

Lifts the error, simple, and hyphenated execution paths of `uuid::parser::try_parse` to
`parserTryParseSpec.keepsFs` on `libsignalSessionCode`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.MainHops.UuidFs

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem fs_writeReg_local (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by
  cases s; cases w <;> cases r <;> rfl

theorem decodeHex32_okFs_from_parser (b : BitVec 64)
    (hooks : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr parserTryParseName +
        bv% (2 ^ 64 + (ls_off% "uuid::parser::decode_hex32") - (ls_off% "uuid::parser::try_parse")))
      decodeHex32Spec.keepsFs := by
  have h :
      (libsignalSessionCode.rebase b hooks).fnAddr parserTryParseName +
        bv% (2 ^ 64 + (ls_off% "uuid::parser::decode_hex32") - (ls_off% "uuid::parser::try_parse")) =
      (libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name := by
    simp only [Program.fnAddr_rebase, parserTryParseName, decodeHex32Name,
      (ls_lemma% fnOff "uuid::parser::try_parse"), (ls_lemma% fnOff "uuid::parser::decode_hex32")]
    bv_arith
  rw [h]
  exact decodeHex32_okFs b hooks

abbrev parserPostFs (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (s0 : State)
    (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ parserTryParseSpec.keepsFs.post (p, bs, out17) s0 sf ∗ R) ∧
    sf.sp = s0.sp ∧
    CalleeSavedPreserved s0 sf

theorem wp_err_fs (b : BitVec 64)
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
    (hfs : s.fs = s0.fs)
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
      (parserPostFs p bs out17 s0 R) := by
  subst entry
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  code_fetches libsignalSessionCode parserTryParseBin b
    hooks
    (ls_lemma% fnOff "uuid::parser::try_parse") (num% (ls_off% "uuid::parser::try_parse")) 536
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "uuid::parser::try_parse" = entry
  examples_hide_fetches
  wp_steps
  unfold parserPostFs Spec.keepsFs parserTryParseSpec
  simp only [huuid, parserTryParseResultAt, stackAt_parser_split s0.sp]
  wp_done

theorem wp_simple_fs (b : BitVec 64)
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
    (hfs : s.fs = s0.fs)
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
      (parserPostFs p bs out17 s0 R) := by
  subst entry
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have hcallee_hex := decodeHex32_okFs_from_parser b hooks
  simp only [Spec.keepsFs, decodeHex32Spec] at hcallee_hex
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
    unfold parserPostFs Spec.keepsFs parserTryParseSpec
    simp only [huuid, hdec, parserTryParseResultAt, stackAt_parser_split s0.sp,
      memRegion_sp88_32_for_simple s0.sp, memRegion_sp88_17_none s0.sp]
    wp_done
  | some u =>
    rw [decodeHex32ResultAt_sp88_some s0.sp u, hsp]
    wp_steps
    unfold parserPostFs Spec.keepsFs parserTryParseSpec
    simp only [huuid, hdec, parserTryParseResultAt_some_eq, stackAt_parser_split s0.sp,
      memRegion_sp88_32_for_simple s0.sp, memRegion_sp88_17_some s0.sp]
    wp_done

set_option maxHeartbeats 800000 in
theorem wp_hyphenated_fs (b : BitVec 64)
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
    (hfs : s.fs = s0.fs)
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
      (parserPostFs p bs out17 s0 R) := by
  subst entry
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have hcallee_hex := decodeHex32_okFs_from_parser b hooks
  simp only [Spec.keepsFs, decodeHex32Spec] at hcallee_hex
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
    unfold parserPostFs Spec.keepsFs parserTryParseSpec
    simp only [hframe, hp19_split p19, huuid, hnone, parserTryParseResultAt,
      stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]
    wp_done
  · wp_steps
    wp_if h13
    · wp_steps
      have hnone := parseHyphenated_ne_13 hph h13
      unfold parserPostFs Spec.keepsFs parserTryParseSpec
      simp only [hframe, hp19_split p19, huuid, hnone, parserTryParseResultAt,
        stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]
      wp_done
    · wp_steps
      wp_if h18
      · wp_steps
        have hnone := parseHyphenated_ne_18 hph h18
        unfold parserPostFs Spec.keepsFs parserTryParseSpec
        simp only [hframe, hp19_split p19, huuid, hnone, parserTryParseResultAt,
          stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]
        wp_done
      · wp_steps
        wp_if h23
        · wp_steps
          have hnone := parseHyphenated_ne_23 hph h23
          unfold parserPostFs Spec.keepsFs parserTryParseSpec
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
            unfold parserPostFs Spec.keepsFs parserTryParseSpec
            simp only [hframe, hp19_split p19, huuid, hall, hdec, parserTryParseResultAt,
              stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp,
              memRegion_sp52_17_none s0.sp]
            wp_done
          | some u =>
            rw [decodeHex32ResultAt_sp52_some s0.sp u, ← hsp_hex32 s0.sp, hsp]
            wp_steps
            unfold parserPostFs Spec.keepsFs parserTryParseSpec
            simp only [hframe, hp19_split p19, huuid, hall, hdec, parserTryParseResultAt_some_eq,
              stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp,
              memRegion_sp52_17_some s0.sp]
            wp_done

end CryptoVerification.SignalSession.Cli.MainHops.UuidFs
