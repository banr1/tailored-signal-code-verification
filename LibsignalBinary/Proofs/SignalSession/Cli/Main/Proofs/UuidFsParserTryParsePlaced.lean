/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsParserHyphenatedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsParserTryParse
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.ParserTryParse
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Relocatable `.keepsFs` Contracts for `uuid::parser::try_parse` and `<uuid::Uuid>::try_parse`

Relocatable (`[LibsignalPlacement]`, Blocks `252` and `255`) `.keepsFs` contracts for
`uuid::parser::try_parse` and `<uuid::Uuid>::try_parse`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.MainHops.UuidFs

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem fs_writeReg_placed (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by
  cases s; cases w <;> cases r <;> rfl

set_option maxHeartbeats 800000 in
theorem wp_braced_fs_placed [LibsignalPlacement]
    (hooks : LibsignalHooks)
    (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8)
    (s0 s : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : s0.spAligned = true)
    (hlen : bs.length = 38)
    (hpc : s.pc = (blkPl_255).base + bv% (388))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = p)
    (hx8 : s.readReg64 .x8 = out17)
    (hx29 : s.readReg64 .x29 = s0.sp - 32#64)
    (htr : s.trace = s0.trace)
    (hfs : s.fs = s0.fs)
    (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks)
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
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have h_hyph := wp_hyphenated_fs_placed hooks
  rcases exists_38_parts bs hlen with ⟨b0, b37, s36, hs36, _, huuid, hp_split⟩
  rw [hp_split p]
  wp_steps
  wp_if hb0
  · wp_steps
    have hnone := braced_ne_0 huuid hb0
    unfold parserPostFs Spec.keepsFs parserTryParseSpec
    simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
    wp_done
  · wp_steps
    wp_if hb37
    · wp_steps
      have hnone := braced_ne_37 huuid hb37
      unfold parserPostFs Spec.keepsFs parserTryParseSpec
      simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
      wp_done
    · wp_step
      wp_step
      have hall := braced_all_eq huuid hb0 hb37
      exact h_hyph p (p + 1#64) bs s36
        ((p ↦₈ b0) ∗ ((p + 37#64) ↦₈ b37)) out17 R out_w0 out_w1 out_b2 s0 _
        (by convert hcl0 using 1; wp_norm_lhs)
        hsp_align hs36 (hp_split p) hall
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
         by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩

set_option maxHeartbeats 800000 in
theorem wp_urn_fs_placed [LibsignalPlacement]
    (hooks : LibsignalHooks)
    (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8)
    (s0 s : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : s0.spAligned = true)
    (hlen : bs.length = 45)
    (hpc : s.pc = (blkPl_255).base + bv% (212))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = p)
    (hx8 : s.readReg64 .x8 = out17)
    (hx29 : s.readReg64 .x29 = s0.sp - 32#64)
    (htr : s.trace = s0.trace)
    (hfs : s.fs = s0.fs)
    (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks)
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
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have h_hyph := wp_hyphenated_fs_placed hooks
  rcases exists_45_parts bs hlen with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, s36, hs36, huuid, hp_split⟩
  rw [hp_split p]
  wp_steps
  wp_if hb0
  · wp_steps
    have hnone : uuidTryParse bs = none := by
      have : 0x75#8 ≠ b0 := fun h => hb0 (by subst h; rfl)
      simp [huuid, this]
    unfold parserPostFs Spec.keepsFs parserTryParseSpec
    simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
    wp_done
  · wp_steps
    wp_if hb1
    · wp_steps
      have hnone : uuidTryParse bs = none := by
        have : 0x72#8 ≠ b1 := fun h => hb1 (by subst h; rfl)
        simp [huuid, this]
      unfold parserPostFs Spec.keepsFs parserTryParseSpec
      simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
      wp_done
    · wp_steps
      wp_if hb2
      · wp_steps
        have hnone : uuidTryParse bs = none := by
          have : 0x6e#8 ≠ b2 := fun h => hb2 (by subst h; rfl)
          simp [huuid, this]
        unfold parserPostFs Spec.keepsFs parserTryParseSpec
        simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
        wp_done
      · wp_steps
        wp_if hb3
        · wp_steps
          have hnone : uuidTryParse bs = none := by
            have : 0x3a#8 ≠ b3 := fun h => hb3 (by subst h; rfl)
            simp [huuid, this]
          unfold parserPostFs Spec.keepsFs parserTryParseSpec
          simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
          wp_done
        · wp_steps
          wp_if hb4
          · wp_steps
            have hnone : uuidTryParse bs = none := by
              have : 0x75#8 ≠ b4 := fun h => hb4 (by subst h; rfl)
              simp [huuid, this]
            unfold parserPostFs Spec.keepsFs parserTryParseSpec
            simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
            wp_done
          · wp_steps
            wp_if hb5
            · wp_steps
              have hnone : uuidTryParse bs = none := by
                have : 0x75#8 ≠ b5 := fun h => hb5 (by subst h; rfl)
                simp [huuid, this]
              unfold parserPostFs Spec.keepsFs parserTryParseSpec
              simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
              wp_done
            · wp_steps
              wp_if hb6
              · wp_steps
                have hnone : uuidTryParse bs = none := by
                  have : 0x69#8 ≠ b6 := fun h => hb6 (by subst h; rfl)
                  simp [huuid, this]
                unfold parserPostFs Spec.keepsFs parserTryParseSpec
                simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
                wp_done
              · wp_steps
                wp_if hb7
                · wp_steps
                  have hnone : uuidTryParse bs = none := by
                    have : 0x64#8 ≠ b7 := fun h => hb7 (by subst h; rfl)
                    simp [huuid, this]
                  unfold parserPostFs Spec.keepsFs parserTryParseSpec
                  simp only [hp_split p, hnone, parserTryParseResultAt, stackAt_parser_split s0.sp]
                  wp_done
                · wp_steps
                  wp_if hb8
                  · wp_steps
                    have hnone : uuidTryParse bs = none := by
                      have : 0x3a#8 ≠ b8 := fun h => hb8 (by subst h; rfl)
                      simp [huuid, this]
                    unfold parserPostFs Spec.keepsFs parserTryParseSpec
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
                      (by convert hcl0 using 1; wp_norm_lhs)
                      hsp_align hs36 (hp_split p) hall
                      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
                      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
                      (by wp_norm_lhs) (by wp_norm_lhs)
                      ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
                       by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩

set_option maxHeartbeats 800000 in
theorem parserTryParse_placed_okFs [LibsignalPlacement]
    (hooks : LibsignalHooks) :
    subroutine_ok ((blkPC_255).rebase (blkPl_255).base hooks)
      (blkPl_255).base
      (withLsCodeLoaded lsmpl parserTryParseSpec.keepsFs) := by
  apply subroutine_ok_of_sepWP_simple
  intro ⟨p, bs, out17⟩ R s0 hpc hrun hsp
  change SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s0
    (((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧ s0.readReg64 .x8 = out17⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out17 17) ∗ stackAt s0.sp 0x80) ∗
      ⌜LibsignalCodeLoaded lsmpl s0.mem⌝)
    (parserPostFs p bs out17 s0 R)
  rw [sepConj_comm]
  apply SepWP.pure_elim; intro hcl0
  have h_braced := wp_braced_fs_placed hooks
  have h_urn := wp_urn_fs_placed hooks
  have h_simple := wp_simple_fs_placed hooks
  have h_hyph := wp_hyphenated_fs_placed hooks
  have h_err := wp_err_fs_placed hooks
  simp only [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hx0, hx1, hx8⟩
  rw [memRegion_out17_split out17, stackAt_parser_split s0.sp]
  wp_pull_exists
  apply sepWP_seq_lscl hcl0 (mid := (blkPl_255).base + bv% (16))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_steps
  wp_if hgt
  · have hne32 : bs.length ≠ 32 := by
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
    · have hlen38 : bs.length = 38 := len_eq_of_reg_eq hx1 heq38
      apply sepWP_parser_branch
      refine h_braced p bs out17 R _ _ _ s0 _
        (by convert hcl1 using 1; wp_norm_lhs)
        hsp hlen38 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
    · have hne38 : bs.length ≠ 38 := len_ne_of_reg_ne hx1 heq38
      wp_steps
      wp_if hne45_reg
      · have hne45 : bs.length ≠ 45 := len_ne_of_reg_ne hx1 hne45_reg
        have huuid := uuidTryParse_of_other_len hne32 hne36 hne38 hne45
        apply sepWP_parser_branch
        refine h_err p bs out17 R _ _ _ s0 _
          hsp huuid ?_ ?_ ?_ ?_ ?_ ?_
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
      · have hlen45 : bs.length = 45 := len_eq_of_reg_eq hx1 hne45_reg
        apply sepWP_parser_branch
        refine h_urn p bs out17 R _ _ _ s0 _
          (by convert hcl1 using 1; wp_norm_lhs)
          hsp hlen45 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
  · have hne38 : bs.length ≠ 38 := by
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
    · have hlen32 : bs.length = 32 := len_eq_of_reg_eq hx1 heq32
      apply sepWP_parser_branch
      refine h_simple p bs out17 R _ _ _ s0 _
        (by convert hcl1 using 1; wp_norm_lhs)
        hsp hlen32 ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
    · have hne32 : bs.length ≠ 32 := len_ne_of_reg_ne hx1 heq32
      wp_steps
      wp_if hne36_reg
      · have hne36 : bs.length ≠ 36 := len_ne_of_reg_ne hx1 hne36_reg
        have huuid := uuidTryParse_of_other_len hne32 hne36 hne38 hne45
        apply sepWP_parser_branch
        refine h_err p bs out17 R _ _ _ s0 _
          hsp huuid ?_ ?_ ?_ ?_ ?_ ?_
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
      · have hlen36 : bs.length = 36 := len_eq_of_reg_eq hx1 hne36_reg
        have huuid : uuidTryParse bs = parseHyphenated bs := by
          unfold uuidTryParse
          simp [hlen36]
        have hframe : (p ↦ₛ bs) = ((p ↦ₛ bs) ∗ emp) := (sepConj_emp (p ↦ₛ bs)).symm
        apply sepWP_parser_hyph36
        refine h_hyph p p bs bs emp out17 R _ _ _ s0 _
          (by convert hcl1 using 1; wp_norm_lhs)
          hsp hlen36 hframe huuid ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs

theorem uuidTryParse_placed_okFs_impl [LibsignalPlacement]
    (hooks : LibsignalHooks) :
    subroutine_ok ((blkPC_252).rebase (blkPl_252).base hooks)
      (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse).keepsFs) := by
  have hcallee := ls_subroutine_ok_cl_of_block
    (callerProg := (blkPC_252).rebase (blkPl_252).base hooks) (parserTryParse_placed_okFs hooks)
  change subroutine_ok _ (lsmpl.base 255) _ at hcallee
  simp only [withLsCl, Spec.keepsFs, parserTryParseSpec, sepConj_assoc] at hcallee
  apply subroutine_ok_of_sepWP_simple
  intro ⟨p, bs, out⟩ R s0 hpc hrun hsp
  dsimp only [withLsCodeLoaded, Spec.keepsFs, uuidTryParseCodeSpec, uuidTryParseSpec,
    BitVec.ofNat_eq_ofNat] at *
  rw [sepConj_comm]
  apply SepWP.pure_elim; intro hcl0
  simp only [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hx0, hx1, hx8⟩
  rw [memRegion_out32_split out, stackAt_uuid_split s0.sp]
  wp_pull_exists
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 255)
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro _hcl_call
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

end CryptoVerification.SignalSession.Cli.MainHops.UuidFs
