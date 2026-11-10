/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec.CoreFromUtf8
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import VerifiedLibraries.RustStd.Proofs.Wave2.FromUtf8
import ProofLib

/-!
# Single-Block Read-Only Slice Stepping for `from_utf8` (`HooksDehook.FromUtf8SingleBlockRO`)

Proves `pureWordsProg_rawCoreFromUtf8RO_ok` directly over the `156`-word single-block placement
`fromUtf8Block.Placeable pl` (`0` dependency on other blocks of `coreMultiLib`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlockRO

open Arm64 Arm64.Obj Arm64.Process ProofLib
open ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open VerifiedLibraries.RustStd (FuLoopRegs FuPreserved bv64_ofNat_add_small
  coreFromUtf8ROSpec corePlacedData1 corePlacedData1_length coreUtf8CharWidthSym
  drop_eq_nil_of_eq_len fromUtf8SretPost fu_ule_false fu_ule_true isUtf8ContByte
  memRegion18_eq pointsToBytesRO_focus8 runUtf8Validation runUtf8ValidationLoop
  runUtf8ValidationLoop_err_lead runUtf8ValidationLoop_step_ascii
  runUtf8ValidationLoop_swar16 runUtf8ValidationLoop_width2_eof
  runUtf8ValidationLoop_width2_step runUtf8ValidationLoop_width3_eof1
  runUtf8ValidationLoop_width3_eof2 runUtf8ValidationLoop_width3_err1
  runUtf8ValidationLoop_width3_step runUtf8ValidationLoop_width4_eof1
  runUtf8ValidationLoop_width4_eof2 runUtf8ValidationLoop_width4_eof3
  runUtf8ValidationLoop_width4_err1 runUtf8ValidationLoop_width4_err2
  runUtf8ValidationLoop_width4_step rustSepWP_cut signExtend32_and_ff64 sret_tail8_merge
  truncate32_signExtend64 utf8AlignOff utf8CharWidth_eq_2_iff utf8CharWidth_eq_3_iff
  utf8CharWidth_eq_4_iff utf8CharWidth_zeroExtend32_eq utf8ErrorLenAt utf8Width3Ok2
  utf8Width4Ok2)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock
  (fromUtf8Block fromUtf8PatchedWords SingleFromUtf8Pl sfuPl sfuPC
   subroutine_ok_pureWords_of_sfuRebase
   fu_cmn41_le fu_cmn41_gt fu_cmn40_lt fu_cmn40_ge fu_cmn61_le fu_cmn71_le
   fu_byte32_beq fu_byte32_bne fu_e0_mask_eq fu_f0_sub_ult
   fu_e_ee_ef_ne_false fu_f_f1_f3_hi_false fu_multibyte_and64
   fu_tbnz31_64 fu_tbnz31_32 fu_tbnz31_se fu_bne_len fu_ule_sub15 fu_sub15_csel)

/-! ## 1. Read-Only 16-Byte Slice Window Focus & Pure Condition-Code Helpers -/

private theorem pointsToBytesRO_focus16_at (p : BitVec 64) (bs : List (BitVec 8)) {idx : Nat}
    (h16 : idx + 16 ≤ bs.length) :
    ∃ w0 w1 : BitVec 64,
      (bs.drop idx).take 16 = unpack64 w0 ++ unpack64 w1 ∧
      (p ↦ᵣ bs) = ((p + BitVec.ofNat 64 idx) ↦₆₄ᵣ w0) ∗ (((p + BitVec.ofNat 64 idx) + 8#64) ↦₆₄ᵣ w1) ∗
        ((p ↦ᵣ bs.take idx) ∗ ((p + BitVec.ofNat 64 (idx + 16)) ↦ᵣ bs.drop (idx + 16))) := by
  have hlen16 : ((bs.drop idx).take 16).length = 16 := by simp; omega
  obtain ⟨w0, w1, hchunk, _⟩ := exists_unpack64_of_length_16 hlen16
  refine ⟨w0, w1, hchunk, ?_⟩
  rw [pointsToBytesRO_split3 p bs idx 16 h16, hchunk, pointsToBytesRO_append,
      show (unpack64 w0).length = 8 from rfl, show BitVec.ofNat 64 8 = 8#64 from rfl,
      ← pointsTo64RO_eq_pointsToBytesRO, ← pointsTo64RO_eq_pointsToBytesRO]
  sep_ac_rfl

private theorem fu_tbnz31_ascii {b0 : BitVec 8} (hb0 : b0 < 0x80#8) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b0))).getLsbD 31 = false ∧
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b0)))).getLsbD 31 = false ∧
    (b0.signExtend 32).getLsbD 31 = false := by
  refine ⟨?_, ?_, ?_⟩
  · rw [fu_tbnz31_64, decide_eq_true hb0]; rfl
  · rw [fu_tbnz31_32, decide_eq_true hb0]; rfl
  · rw [fu_tbnz31_se, decide_eq_true hb0]; rfl

private theorem fu_tbnz31_nonAscii {b0 : BitVec 8} (hb0 : ¬ (b0 < 0x80#8)) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b0))).getLsbD 31 = true ∧
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b0)))).getLsbD 31 = true ∧
    (b0.signExtend 32).getLsbD 31 = true := by
  refine ⟨?_, ?_, ?_⟩
  · rw [fu_tbnz31_64, decide_eq_false hb0]; rfl
  · rw [fu_tbnz31_32, decide_eq_false hb0]; rfl
  · rw [fu_tbnz31_se, decide_eq_false hb0]; rfl

section
arm64_proof_prelude

local macro "fu_step_pres " h:term:max hr:term:max : term =>
  `(FuPreserved.step $h (by simpa [arm64_norm] using $hr) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [CalleeSavedPreserved, calleeSavedVRegs, arm64_norm]))

local macro "fu_keep_regs " h:term:max hr:term:max : term =>
  `(FuLoopRegs.preserve $h (by simpa [arm64_norm] using $hr) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [CalleeSavedPreserved, calleeSavedVRegs, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]))

/-! ## 2. Read-Only Precondition, Postcondition Continuation & Return Blocks (`+0x1ec .. +0x26c`) -/

private def fuWorkPreRO (p tbl ret : BitVec 64) (bs : List (BitVec 8))
    (s0 s8 : BitVec 64) (s16 s17 : BitVec 8) (b18 : BitVec 16) (b20 : BitVec 32) : SepProp :=
  (p ↦ᵣ bs) ∗ (tbl ↦ᵣ corePlacedData1) ∗ (ret ↦₆₄ s0) ∗ ((ret + 8#64) ↦₆₄ s8) ∗
  ((ret + 16#64) ↦₈ s16) ∗ ((ret + 17#64) ↦₈ s17) ∗ ((ret + 18#64) ↦₁₆ b18) ∗ ((ret + 20#64) ↦₃₂ b20)

private def fuPostPropRO (p tbl ret : BitVec 64) (bs : List (BitVec 8))
    (b18 : BitVec 16) (b20 : BitVec 32) : SepProp :=
  (p ↦ᵣ bs) ∗ (tbl ↦ᵣ corePlacedData1) ∗ fromUtf8SretPost ret p bs.length b18 b20 (runUtf8Validation bs)

private abbrev FuPostContRO (s_entry : State) (p tbl ret : BitVec 64) (bs : List (BitVec 8))
    (b18 : BitVec 16) (b20 : BitVec 32) (post : State → SepProp → Prop) : Prop :=
  ∀ (sf : State) (Q : SepProp), FuPreserved s_entry sf → sf.pc = s_entry.readReg64 .lr →
    (Q ⊢ fuPostPropRO p tbl ret bs b18 b20) → post sf Q

private abbrev FuNextContRO [SingleFromUtf8Pl] (s_entry : State)
    (p tbl ret s0 s8 : BitVec 64) (s16 s17 : BitVec 8) (b18 : BitVec 16) (b20 : BitVec 32)
    (bs : List (BitVec 8)) (idx : Nat) (post : State → SepProp → Prop) : Prop :=
  ∀ (idx' : Nat) (sn : State), idx < idx' → idx' ≤ bs.length →
    runUtf8Validation bs = runUtf8ValidationLoop idx' (bs.drop idx') → sn.pc = sfuPl.base + 44#64 →
    FuLoopRegs s_entry sn p tbl ret bs.length idx' →
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) sn
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post

private theorem FuNextContRO.mono [SingleFromUtf8Pl] {s_entry : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx idx1 : Nat} {post : State → SepProp → Prop} (hle : idx ≤ idx1)
    (h : FuNextContRO s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post) :
    FuNextContRO s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx1 post :=
  fun idx' sn hlt => h idx' sn (by omega)

private theorem fuRetOkRO [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {post : State → SepProp → Prop}
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post) (hok : runUtf8Validation bs = .ok ())
    (hpc : s.pc = sfuPl.base + 524#64) (hpres : FuPreserved s_entry s)
    (hx0 : s.readReg64 .x0 = p) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs.length)
    (hx8 : s.readReg64 .x8 = ret) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running; have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPreRO, sret_tail8_merge ret s16 s17 b18 b20]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) (hpost _ _ (fu_step_pres hpres hrun) rfl ?_)
  dsimp only [fuPostPropRO]; rw [hok]; dsimp only [fromUtf8SretPost]; sep_entail

private theorem fuRetErrNoneRO [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := none })
    (hpc : s.pc = sfuPl.base + 536#64) (hpres : FuPreserved s_entry s)
    (hx8 : s.readReg64 .x8 = ret) (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running; have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPreRO]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) (hpost _ _ (fu_step_pres hpres hrun) rfl ?_)
  dsimp only [fuPostPropRO]; rw [herr]; dsimp only [fromUtf8SretPost, utf8ErrorLenAt]
  rw [show (ret + 16#64) + 1#64 = ret + 17#64 by bv_lin]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_right (BitVec.setWidth 8 (s.readReg64 (.gpr 13#5))) (by sep_entail)

private theorem fuRetErrSomeRO_1f4 [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 k : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some k })
    (hpc : s.pc = sfuPl.base + 500#64) (hpres : FuPreserved s_entry s)
    (hx8 : s.readReg64 .x8 = ret) (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx)
    (hx14 : BitVec.setWidth 8 (s.readReg64 (.gpr 14#5)) = 1#8)
    (hx13 : BitVec.setWidth 8 (s.readReg64 (.gpr 13#5)) = k) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running; have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPreRO]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) (hpost _ _ (fu_step_pres hpres hrun) rfl ?_)
  dsimp only [fuPostPropRO]; rw [herr]; dsimp only [fromUtf8SretPost, utf8ErrorLenAt]
  rw [show (ret + 16#64) + 1#64 = ret + 17#64 by bv_lin]; sep_entail

private theorem fuRetErr2RO_1ec [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some 2#8 })
    (hpc : s.pc = sfuPl.base + 492#64) (hpres : FuPreserved s_entry s)
    (hx8 : s.readReg64 .x8 = ret) (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running
  apply rustSepWP_cut (mid := sfuPl.base + 500#64); wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  exact fuRetErrSomeRO_1f4 hpost herr rfl (fu_step_pres hpres hrun)
    (by simp [arm64_norm, hx8]) (by simp [arm64_norm, hx9]) (by simp [arm64_norm]) (by simp [arm64_norm])

private theorem fuRetErr1RO_230 [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some 1#8 })
    (hpc : s.pc = sfuPl.base + 560#64) (hpres : FuPreserved s_entry s)
    (hx8 : s.readReg64 .x8 = ret) (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running; have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPreRO]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) (hpost _ _ (fu_step_pres hpres hrun) rfl ?_)
  dsimp only [fuPostPropRO]; rw [herr]; dsimp only [fromUtf8SretPost, utf8ErrorLenAt]
  rw [show (ret + 16#64) + 1#64 = ret + 17#64 by bv_lin]; sep_entail

private theorem fuRetErr3RO_250 [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some 3#8 })
    (hpc : s.pc = sfuPl.base + 592#64) (hpres : FuPreserved s_entry s)
    (hx8 : s.readReg64 .x8 = ret) (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running; have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPreRO]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) (hpost _ _ (fu_step_pres hpres hrun) rfl ?_)
  dsimp only [fuPostPropRO]; rw [herr]; dsimp only [fromUtf8SretPost, utf8ErrorLenAt]
  rw [show (ret + 16#64) + 1#64 = ret + 17#64 by bv_lin]; sep_entail

/-! ## 3. Multi-Byte UTF-8 Sequence Validation (`+0x90 .. +0x1e8`) -/

private theorem fuWidth2RO [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop} (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextContRO s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length) (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hw2 : (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = true)
    (hpc : s.pc = sfuPl.base + 180#64) (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
  by_cases h1 : idx + 1 < bs.length
  · have hptr1 : p + (BitVec.ofNat 64 idx + 1#64) = p + BitVec.ofNat 64 (idx + 1) := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = false := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
      exact fu_ule_false h1 hlen
    have hse1 := truncate32_signExtend64 (bs.getD (idx + 1) 0#8)
    have hstep := hval.trans (runUtf8ValidationLoop_width2_step h1 hw2)
    cases hc1 : isUtf8ContByte (bs.getD (idx + 1) 0#8)
    · have herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some 1#8 } := by
        simpa only [hc1, Bool.false_eq_true, ↓reduceIte] using hstep
      have hle_c : ConditionHolds .LE (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x41#32) = false := by
        rw [fu_cmn41_le]; exact hc1
      apply rustSepWP_cut (mid := sfuPl.base + 560#64)
      wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs (idx + 1) h1, ← hptr1]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr1, ← pointsToBytesRO_focus8 p bs (idx + 1) h1, ← fuWorkPreRO]
      exact fuRetErr1RO_230 hpost herr rfl (fu_step_pres hregs.pres hrun)
        (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])
    · have hok2 : runUtf8Validation bs = runUtf8ValidationLoop (idx + 2) (bs.drop (idx + 2)) := by
        simpa only [hc1, ↓reduceIte] using hstep
      have hle_c : ConditionHolds .LE (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x41#32) = true := by
        rw [fu_cmn41_le]; exact hc1
      apply rustSepWP_cut (mid := sfuPl.base + 44#64)
      wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs (idx + 1) h1, ← hptr1]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr1, ← pointsToBytesRO_focus8 p bs (idx + 1) h1, ← fuWorkPreRO]
      refine hnext (idx + 2) _ (by omega) (by omega) hok2 rfl
        ⟨fu_step_pres hregs.pres hrun, by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
          by simp [arm64_norm, hregs.x8_eq], ?_, by simp [arm64_norm, hregs.x10_eq],
          by simp [arm64_norm, hregs.x11_eq], by simp [arm64_norm, hregs.x12_eq]⟩
      simpa only [arm64_norm] using bv64_ofNat_add_small idx 2
  · have heof : idx + 1 = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = true := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small, heof]
      exact fu_ule_true
    apply rustSepWP_cut (mid := sfuPl.base + 536#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetErrNoneRO hpost (hval.trans (runUtf8ValidationLoop_width2_eof hidx heof hw2)) rfl
      (fu_step_pres hregs.pres hrun) (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])

private theorem fuWidth3TailRO [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop} (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextContRO s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx1 : idx + 1 < bs.length) (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hw3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = true)
    (hok2 : utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = true)
    (hpc : s.pc = sfuPl.base + 468#64) (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
  by_cases h2 : idx + 2 < bs.length
  · have hptr2 : p + (BitVec.ofNat 64 idx + 2#64) = p + BitVec.ofNat 64 (idx + 2) := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small]
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 2#64) = false := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small]
      exact fu_ule_false h2 hlen
    have hse2 := truncate32_signExtend64 (bs.getD (idx + 2) 0#8)
    have hstep := hval.trans (runUtf8ValidationLoop_width3_step h2 hw3 hok2)
    cases hc2 : isUtf8ContByte (bs.getD (idx + 2) 0#8)
    · have herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some 2#8 } := by
        simpa only [hc2, Bool.false_eq_true, ↓reduceIte] using hstep
      have hle_c : ConditionHolds .LE (addsPState32 ((bs.getD (idx + 2) 0#8).signExtend 32) 0x41#32) = false := by
        rw [fu_cmn41_le]; exact hc2
      apply rustSepWP_cut (mid := sfuPl.base + 492#64)
      wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs (idx + 2) h2, ← hptr2]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr2, ← pointsToBytesRO_focus8 p bs (idx + 2) h2, ← fuWorkPreRO]
      exact fuRetErr2RO_1ec hpost herr rfl (fu_step_pres hregs.pres hrun)
        (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])
    · have hok3 : runUtf8Validation bs = runUtf8ValidationLoop (idx + 3) (bs.drop (idx + 3)) := by
        simpa only [hc2, ↓reduceIte] using hstep
      have hle_c : ConditionHolds .LE (addsPState32 ((bs.getD (idx + 2) 0#8).signExtend 32) 0x41#32) = true := by
        rw [fu_cmn41_le]; exact hc2
      apply rustSepWP_cut (mid := sfuPl.base + 44#64)
      wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs (idx + 2) h2, ← hptr2]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr2, ← pointsToBytesRO_focus8 p bs (idx + 2) h2, ← fuWorkPreRO]
      refine hnext (idx + 3) _ (by omega) (by omega) hok3 rfl
        ⟨fu_step_pres hregs.pres hrun, by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
          by simp [arm64_norm, hregs.x8_eq], ?_, by simp [arm64_norm, hregs.x10_eq],
          by simp [arm64_norm, hregs.x11_eq], by simp [arm64_norm, hregs.x12_eq]⟩
      simpa only [arm64_norm] using bv64_ofNat_add_small idx 3
  · have heof2 : idx + 2 = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 2#64) = true := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small, heof2]
      exact fu_ule_true
    apply rustSepWP_cut (mid := sfuPl.base + 536#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetErrNoneRO hpost (hval.trans (runUtf8ValidationLoop_width3_eof2 hidx1 heof2 hw3 hok2)) rfl
      (fu_step_pres hregs.pres hrun) (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])

private theorem fuWidth3RO [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop} (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextContRO s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length) (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hw3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = true)
    (hpc : s.pc = sfuPl.base + 208#64) (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx)
    (hx13 : BitVec.truncate 32 (s.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8)) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
  by_cases h1 : idx + 1 < bs.length
  · have hptr1 : p + (BitVec.ofNat 64 idx + 1#64) = p + BitVec.ofNat 64 (idx + 1) := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = false := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
      exact fu_ule_false h1 hlen
    have hcut_e0 : ∀ sm : State, sm.pc = sfuPl.base + 224#64 →
        FuLoopRegs s_entry sm p tbl ret bs.length idx →
        BitVec.truncate 32 (sm.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8) →
        sm.readReg64 (.gpr 14#5) = (bs.getD (idx + 1) 0#8).zeroExtend 64 →
        SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) sm
          (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
      intro sm hpc_m hregs_m hx13_m hx14_m
      have hrun_m := hregs_m.pres.running
      cases hb0_e0 : (bs.getD idx 0#8 == 0xe0#8)
      · have heq_e0 : (BitVec.setWidth 32 (bs.getD idx 0#8) == 0xe0#32) = false := by
          rw [fu_byte32_beq _ 0xe0#32 (by decide)]; exact hb0_e0
        have hcut_ec : ∀ sn : State, sn.pc = sfuPl.base + 236#64 →
            FuLoopRegs s_entry sn p tbl ret bs.length idx →
            BitVec.truncate 32 (sn.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8) →
            BitVec.truncate 32 (sn.readReg64 (.gpr 14#5)) = (bs.getD (idx + 1) 0#8).signExtend 32 →
            SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) sn
              (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
          intro sn hpc_n hregs_n hx13_n hx14_n
          have hrun_n := hregs_n.pres.running
          cases hb0_ed : (bs.getD idx 0#8 == 0xed#8)
          · have hne_ed : (BitVec.setWidth 32 (bs.getD idx 0#8) != 0xed#32) = true := by
              rw [fu_byte32_bne _ 0xed#32 (by decide), show BitVec.ofNat 8 (0xed#32).toNat = 0xed#8 from rfl, hb0_ed]; rfl
            have hok2_eq : utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = isUtf8ContByte (bs.getD (idx + 1) 0#8) := by
              simp only [utf8Width3Ok2, hb0_e0, hb0_ed, Bool.false_eq_true, ↓reduceIte]
            cases hcs_e1 : BitVec.ule 0x0c#32 (BitVec.setWidth 32 (bs.getD idx 0#8) - 0xe1#32)
            · cases hc1 : isUtf8ContByte (bs.getD (idx + 1) 0#8)
              · have hlt_c : ConditionHolds .LT (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = false := by
                  rw [fu_cmn40_lt]; exact hc1
                have herr := hval.trans (runUtf8ValidationLoop_width3_err1 h1 hw3 (hok2_eq.trans hc1))
                apply rustSepWP_cut (mid := sfuPl.base + 560#64); wp_sym_steps
                refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
                exact fuRetErr1RO_230 hpost herr rfl (fu_step_pres hregs_n.pres hrun_n)
                  (by simp [arm64_norm, hregs_n.x8_eq]) (by simp [arm64_norm, hregs_n.x9_eq])
              · have hlt_c : ConditionHolds .LT (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = true := by
                  rw [fu_cmn40_lt]; exact hc1
                apply rustSepWP_cut (mid := sfuPl.base + 468#64); wp_sym_steps
                refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
                exact fuWidth3TailRO hlen hpost hnext h1 hval hw3 (hok2_eq.trans hc1) rfl (fu_keep_regs hregs_n hrun_n)
            · have hne_ee := fu_e_ee_ef_ne_false (bs.getD idx 0#8) hw3 hb0_e0 hb0_ed hcs_e1
              cases hc1 : isUtf8ContByte (bs.getD (idx + 1) 0#8)
              · have hge_c : ConditionHolds .GE (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = true := by
                  rw [fu_cmn40_ge, hc1]; rfl
                have herr := hval.trans (runUtf8ValidationLoop_width3_err1 h1 hw3 (hok2_eq.trans hc1))
                apply rustSepWP_cut (mid := sfuPl.base + 500#64); wp_sym_steps
                refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
                exact fuRetErrSomeRO_1f4 hpost herr rfl (fu_step_pres hregs_n.pres hrun_n)
                  (by simp [arm64_norm, hregs_n.x8_eq]) (by simp [arm64_norm, hregs_n.x9_eq])
                  (by simp [arm64_norm]) (by simp [arm64_norm])
              · have hge_c : ConditionHolds .GE (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = false := by
                  rw [fu_cmn40_ge, hc1]; rfl
                apply rustSepWP_cut (mid := sfuPl.base + 468#64); wp_sym_steps
                refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
                exact fuWidth3TailRO hlen hpost hnext h1 hval hw3 (hok2_eq.trans hc1) rfl (fu_keep_regs hregs_n hrun_n)
          · have hne_ed : (BitVec.setWidth 32 (bs.getD idx 0#8) != 0xed#32) = false := by
              rw [fu_byte32_bne _ 0xed#32 (by decide), show BitVec.ofNat 8 (0xed#32).toNat = 0xed#8 from rfl, hb0_ed]; rfl
            have hok2_eq : utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
                (0x80#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0x9f#8) := by
              simp only [utf8Width3Ok2, hb0_e0, hb0_ed, Bool.false_eq_true, ↓reduceIte]
            cases hed_ok : (0x80#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0x9f#8)
            · have hle_c : ConditionHolds .LE (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x61#32) = false := by
                rw [fu_cmn61_le]; exact hed_ok
              have herr := hval.trans (runUtf8ValidationLoop_width3_err1 h1 hw3 (hok2_eq.trans hed_ok))
              apply rustSepWP_cut (mid := sfuPl.base + 560#64); wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact fuRetErr1RO_230 hpost herr rfl (fu_step_pres hregs_n.pres hrun_n)
                (by simp [arm64_norm, hregs_n.x8_eq]) (by simp [arm64_norm, hregs_n.x9_eq])
            · have hle_c : ConditionHolds .LE (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x61#32) = true := by
                rw [fu_cmn61_le]; exact hed_ok
              apply rustSepWP_cut (mid := sfuPl.base + 468#64); wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact fuWidth3TailRO hlen hpost hnext h1 hval hw3 (hok2_eq.trans hed_ok) rfl (fu_keep_regs hregs_n hrun_n)
        apply rustSepWP_cut (mid := sfuPl.base + 236#64); wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
        refine hcut_ec _ rfl (fu_keep_regs hregs_m hrun_m) (by simpa only [arm64_norm] using hx13_m) ?_
        simp only [arm64_norm]; generalize bs.getD (idx + 1) 0#8 = b1; revert b1; decide
      · have heq_e0 : (BitVec.setWidth 32 (bs.getD idx 0#8) == 0xe0#32) = true := by
          rw [fu_byte32_beq _ 0xe0#32 (by decide)]; exact hb0_e0
        have hok2_eq : utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
            (0xa0#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0xbf#8) := by
          simp only [utf8Width3Ok2, hb0_e0, ↓reduceIte]
        cases he0_ok : (0xa0#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0xbf#8)
        · have hm_eq : ((BitVec.setWidth 32 (bs.getD (idx + 1) 0#8) &&& 0xe0#32) == 0xa0#32) = false := by
            rw [fu_e0_mask_eq]; exact he0_ok
          have herr := hval.trans (runUtf8ValidationLoop_width3_err1 h1 hw3 (hok2_eq.trans he0_ok))
          apply rustSepWP_cut (mid := sfuPl.base + 560#64); wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact fuRetErr1RO_230 hpost herr rfl (fu_step_pres hregs_m.pres hrun_m)
            (by simp [arm64_norm, hregs_m.x8_eq]) (by simp [arm64_norm, hregs_m.x9_eq])
        · have hm_eq : ((BitVec.setWidth 32 (bs.getD (idx + 1) 0#8) &&& 0xe0#32) == 0xa0#32) = true := by
            rw [fu_e0_mask_eq]; exact he0_ok
          apply rustSepWP_cut (mid := sfuPl.base + 468#64); wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact fuWidth3TailRO hlen hpost hnext h1 hval hw3 (hok2_eq.trans he0_ok) rfl (fu_keep_regs hregs_m hrun_m)
    apply rustSepWP_cut (mid := sfuPl.base + 224#64)
    wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs (idx + 1) h1, ← hptr1]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    wp_conv_pre => rw [hptr1, ← pointsToBytesRO_focus8 p bs (idx + 1) h1, ← fuWorkPreRO]
    exact hcut_e0 _ rfl (fu_keep_regs hregs hrun) (by simpa only [arm64_norm] using hx13) (by simp [arm64_norm])
  · have heof : idx + 1 = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = true := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small, heof]
      exact fu_ule_true
    apply rustSepWP_cut (mid := sfuPl.base + 536#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetErrNoneRO hpost (hval.trans (runUtf8ValidationLoop_width3_eof1 hidx heof hw3)) rfl
      (fu_step_pres hregs.pres hrun) (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])

private theorem fuWidth4TailRO [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop} (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextContRO s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx1 : idx + 1 < bs.length) (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hw4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = true)
    (hok2 : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = true)
    (hpc : s.pc = sfuPl.base + 388#64) (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
  by_cases h2 : idx + 2 < bs.length
  · have hptr2 : p + (BitVec.ofNat 64 idx + 2#64) = p + BitVec.ofNat 64 (idx + 2) := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small]
    have hcs2 : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 2#64) = false := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small]
      exact fu_ule_false h2 hlen
    have hse2 := truncate32_signExtend64 (bs.getD (idx + 2) 0#8)
    cases hc2 : isUtf8ContByte (bs.getD (idx + 2) 0#8)
    · have hgt_c : ConditionHolds .GT (addsPState32 ((bs.getD (idx + 2) 0#8).signExtend 32) 0x41#32) = true := by
        rw [fu_cmn41_gt, hc2]; rfl
      have herr := hval.trans (runUtf8ValidationLoop_width4_err2 h2 hw4 hok2 hc2)
      apply rustSepWP_cut (mid := sfuPl.base + 492#64)
      wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs (idx + 2) h2, ← hptr2]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr2, ← pointsToBytesRO_focus8 p bs (idx + 2) h2, ← fuWorkPreRO]
      exact fuRetErr2RO_1ec hpost herr rfl (fu_step_pres hregs.pres hrun)
        (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])
    · have hgt_c : ConditionHolds .GT (addsPState32 ((bs.getD (idx + 2) 0#8).signExtend 32) 0x41#32) = false := by
        rw [fu_cmn41_gt, hc2]; rfl
      have hcut_19c : ∀ sm : State, sm.pc = sfuPl.base + 412#64 →
          FuLoopRegs s_entry sm p tbl ret bs.length idx →
          SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) sm
            (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
        intro sm hpc_m hregs_m
        have hrun_m := hregs_m.pres.running; have hx0_m := hregs_m.x0_eq
        have hx1_m := hregs_m.x1_eq; have hx9_m := hregs_m.x9_eq
        by_cases h3 : idx + 3 < bs.length
        · have hptr3 : p + (BitVec.ofNat 64 idx + 3#64) = p + BitVec.ofNat 64 (idx + 3) := by
            rw [show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, bv64_ofNat_add_small]
          have hcs3 : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 3#64) = false := by
            rw [show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, bv64_ofNat_add_small]
            exact fu_ule_false h3 hlen
          have hse3 := truncate32_signExtend64 (bs.getD (idx + 3) 0#8)
          have hstep := hval.trans (runUtf8ValidationLoop_width4_step h3 hw4 hok2 hc2)
          cases hc3 : isUtf8ContByte (bs.getD (idx + 3) 0#8)
          · have herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some 3#8 } := by
              simpa only [hc3, Bool.false_eq_true, ↓reduceIte] using hstep
            have hlt_c : ConditionHolds .LT (addsPState32 ((bs.getD (idx + 3) 0#8).signExtend 32) 0x40#32) = false := by
              rw [fu_cmn40_lt]; exact hc3
            apply rustSepWP_cut (mid := sfuPl.base + 592#64)
            wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs (idx + 3) h3, ← hptr3]
            wp_sym_steps
            refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
            wp_conv_pre => rw [hptr3, ← pointsToBytesRO_focus8 p bs (idx + 3) h3, ← fuWorkPreRO]
            exact fuRetErr3RO_250 hpost herr rfl (fu_step_pres hregs_m.pres hrun_m)
              (by simp [arm64_norm, hregs_m.x8_eq]) (by simp [arm64_norm, hx9_m])
          · have hok4 : runUtf8Validation bs = runUtf8ValidationLoop (idx + 4) (bs.drop (idx + 4)) := by
              simpa only [hc3, ↓reduceIte] using hstep
            have hlt_c : ConditionHolds .LT (addsPState32 ((bs.getD (idx + 3) 0#8).signExtend 32) 0x40#32) = true := by
              rw [fu_cmn40_lt]; exact hc3
            apply rustSepWP_cut (mid := sfuPl.base + 44#64)
            wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs (idx + 3) h3, ← hptr3]
            wp_sym_steps
            refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
            wp_conv_pre => rw [hptr3, ← pointsToBytesRO_focus8 p bs (idx + 3) h3, ← fuWorkPreRO]
            refine hnext (idx + 4) _ (by omega) (by omega) hok4 rfl
              ⟨fu_step_pres hregs_m.pres hrun_m, by simp [arm64_norm, hx0_m], by simp [arm64_norm, hx1_m],
                by simp [arm64_norm, hregs_m.x8_eq], ?_, by simp [arm64_norm, hregs_m.x10_eq],
                by simp [arm64_norm, hregs_m.x11_eq], by simp [arm64_norm, hregs_m.x12_eq]⟩
            simpa only [arm64_norm] using bv64_ofNat_add_small idx 4
        · have heof3 : idx + 3 = bs.length := by omega
          have hcs3 : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 3#64) = true := by
            rw [show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, bv64_ofNat_add_small, heof3]
            exact fu_ule_true
          apply rustSepWP_cut (mid := sfuPl.base + 536#64); wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact fuRetErrNoneRO hpost (hval.trans (runUtf8ValidationLoop_width4_eof3 h2 heof3 hw4 hok2 hc2)) rfl
            (fu_step_pres hregs_m.pres hrun_m) (by simp [arm64_norm, hregs_m.x8_eq]) (by simp [arm64_norm, hx9_m])
      apply rustSepWP_cut (mid := sfuPl.base + 412#64)
      wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs (idx + 2) h2, ← hptr2]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr2, ← pointsToBytesRO_focus8 p bs (idx + 2) h2, ← fuWorkPreRO]
      exact hcut_19c _ rfl (fu_keep_regs hregs hrun)
  · have heof2 : idx + 2 = bs.length := by omega
    have hcs2 : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 2#64) = true := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small, heof2]
      exact fu_ule_true
    apply rustSepWP_cut (mid := sfuPl.base + 536#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetErrNoneRO hpost (hval.trans (runUtf8ValidationLoop_width4_eof2 hidx1 heof2 hw4 hok2)) rfl
      (fu_step_pres hregs.pres hrun) (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])

private theorem fuWidth4RO [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop} (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextContRO s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length) (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hw4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = true)
    (hpc : s.pc = sfuPl.base + 256#64) (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx)
    (hx13 : BitVec.truncate 32 (s.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8)) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
  by_cases h1 : idx + 1 < bs.length
  · have hptr1 : p + (BitVec.ofNat 64 idx + 1#64) = p + BitVec.ofNat 64 (idx + 1) := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = false := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
      exact fu_ule_false h1 hlen
    have hcut_110 : ∀ sm : State, sm.pc = sfuPl.base + 272#64 →
        FuLoopRegs s_entry sm p tbl ret bs.length idx →
        BitVec.truncate 32 (sm.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8) →
        sm.readReg64 (.gpr 14#5) = (bs.getD (idx + 1) 0#8).zeroExtend 64 →
        SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) sm
          (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
      intro sm hpc_m hregs_m hx13_m hx14_m
      have hrun_m := hregs_m.pres.running
      cases hb0_f0 : (bs.getD idx 0#8 == 0xf0#8)
      · have heq_f0 : (BitVec.setWidth 32 (bs.getD idx 0#8) == 0xf0#32) = false := by
          rw [fu_byte32_beq _ 0xf0#32 (by decide)]; exact hb0_f0
        have hcut_11c : ∀ sn : State, sn.pc = sfuPl.base + 284#64 →
            FuLoopRegs s_entry sn p tbl ret bs.length idx →
            BitVec.truncate 32 (sn.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8) →
            BitVec.truncate 32 (sn.readReg64 (.gpr 14#5)) = (bs.getD (idx + 1) 0#8).signExtend 32 →
            SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) sn
              (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
          intro sn hpc_n hregs_n hx13_n hx14_n
          have hrun_n := hregs_n.pres.running
          cases hb0_f4 : (bs.getD idx 0#8 == 0xf4#8)
          · have hne_f4 : (BitVec.setWidth 32 (bs.getD idx 0#8) != 0xf4#32) = true := by
              rw [fu_byte32_bne _ 0xf4#32 (by decide), show BitVec.ofNat 8 (0xf4#32).toNat = 0xf4#8 from rfl, hb0_f4]; rfl
            have hhi_false := fu_f_f1_f3_hi_false (bs.getD idx 0#8) hw4 hb0_f0 hb0_f4
            have hok2_eq : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = isUtf8ContByte (bs.getD (idx + 1) 0#8) := by
              simp only [utf8Width4Ok2, hb0_f0, hb0_f4, Bool.false_eq_true, ↓reduceIte]
            cases hc1 : isUtf8ContByte (bs.getD (idx + 1) 0#8)
            · have hge_c : ConditionHolds .GE (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = true := by
                rw [fu_cmn40_ge, hc1]; rfl
              have herr := hval.trans (runUtf8ValidationLoop_width4_err1 h1 hw4 (hok2_eq.trans hc1))
              apply rustSepWP_cut (mid := sfuPl.base + 500#64); wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact fuRetErrSomeRO_1f4 hpost herr rfl (fu_step_pres hregs_n.pres hrun_n)
                (by simp [arm64_norm, hregs_n.x8_eq]) (by simp [arm64_norm, hregs_n.x9_eq])
                (by simp [arm64_norm]) (by simp [arm64_norm])
            · have hge_c : ConditionHolds .GE (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = false := by
                rw [fu_cmn40_ge, hc1]; rfl
              apply rustSepWP_cut (mid := sfuPl.base + 388#64); wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact fuWidth4TailRO hlen hpost hnext h1 hval hw4 (hok2_eq.trans hc1) rfl (fu_keep_regs hregs_n hrun_n)
          · have hne_f4 : (BitVec.setWidth 32 (bs.getD idx 0#8) != 0xf4#32) = false := by
              rw [fu_byte32_bne _ 0xf4#32 (by decide), show BitVec.ofNat 8 (0xf4#32).toNat = 0xf4#8 from rfl, hb0_f4]; rfl
            have hok2_eq : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
                (0x80#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0x8f#8) := by
              simp only [utf8Width4Ok2, hb0_f0, hb0_f4, Bool.false_eq_true, ↓reduceIte]
            cases hf4_ok : (0x80#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0x8f#8)
            · have hle_c : ConditionHolds .LE (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x71#32) = false := by
                rw [fu_cmn71_le]; exact hf4_ok
              have herr := hval.trans (runUtf8ValidationLoop_width4_err1 h1 hw4 (hok2_eq.trans hf4_ok))
              apply rustSepWP_cut (mid := sfuPl.base + 560#64); wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact fuRetErr1RO_230 hpost herr rfl (fu_step_pres hregs_n.pres hrun_n)
                (by simp [arm64_norm, hregs_n.x8_eq]) (by simp [arm64_norm, hregs_n.x9_eq])
            · have hle_c : ConditionHolds .LE (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x71#32) = true := by
                rw [fu_cmn71_le]; exact hf4_ok
              apply rustSepWP_cut (mid := sfuPl.base + 388#64); wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact fuWidth4TailRO hlen hpost hnext h1 hval hw4 (hok2_eq.trans hf4_ok) rfl (fu_keep_regs hregs_n hrun_n)
        apply rustSepWP_cut (mid := sfuPl.base + 284#64); wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
        refine hcut_11c _ rfl (fu_keep_regs hregs_m hrun_m) (by simpa only [arm64_norm] using hx13_m) ?_
        simp only [arm64_norm]; generalize bs.getD (idx + 1) 0#8 = b1; revert b1; decide
      · have heq_f0 : (BitVec.setWidth 32 (bs.getD idx 0#8) == 0xf0#32) = true := by
          rw [fu_byte32_beq _ 0xf0#32 (by decide)]; exact hb0_f0
        have hok2_eq : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
            (0x90#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0xbf#8) := by
          simp only [utf8Width4Ok2, hb0_f0, ↓reduceIte]
        cases hf0_ok : (0x90#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0xbf#8)
        · have hcc : BitVec.ult (BitVec.setWidth 32 (bs.getD (idx + 1) 0#8) - 0x90#32) 0x30#32 = false := by
            rw [fu_f0_sub_ult]; exact hf0_ok
          have herr := hval.trans (runUtf8ValidationLoop_width4_err1 h1 hw4 (hok2_eq.trans hf0_ok))
          apply rustSepWP_cut (mid := sfuPl.base + 560#64); wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact fuRetErr1RO_230 hpost herr rfl (fu_step_pres hregs_m.pres hrun_m)
            (by simp [arm64_norm, hregs_m.x8_eq]) (by simp [arm64_norm, hregs_m.x9_eq])
        · have hcc : BitVec.ult (BitVec.setWidth 32 (bs.getD (idx + 1) 0#8) - 0x90#32) 0x30#32 = true := by
            rw [fu_f0_sub_ult]; exact hf0_ok
          apply rustSepWP_cut (mid := sfuPl.base + 388#64); wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact fuWidth4TailRO hlen hpost hnext h1 hval hw4 (hok2_eq.trans hf0_ok) rfl (fu_keep_regs hregs_m hrun_m)
    apply rustSepWP_cut (mid := sfuPl.base + 272#64)
    wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs (idx + 1) h1, ← hptr1]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    wp_conv_pre => rw [hptr1, ← pointsToBytesRO_focus8 p bs (idx + 1) h1, ← fuWorkPreRO]
    exact hcut_110 _ rfl (fu_keep_regs hregs hrun) (by simpa only [arm64_norm] using hx13) (by simp [arm64_norm])
  · have heof : idx + 1 = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = true := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small, heof]
      exact fu_ule_true
    apply rustSepWP_cut (mid := sfuPl.base + 536#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetErrNoneRO hpost (hval.trans (runUtf8ValidationLoop_width4_eof1 hidx heof hw4)) rfl
      (fu_step_pres hregs.pres hrun) (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])

private theorem fuMultiByteRO [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop} (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextContRO s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length) (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hnonAscii : ¬ (bs.getD idx 0#8 < 0x80#8)) (hpc : s.pc = sfuPl.base + 144#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx)
    (hx13 : s.readReg64 (.gpr 13#5) = BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (bs.getD idx 0#8)))) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running; have hx12 := hregs.x12_eq
  have hb0_lt : (bs.getD idx 0#8).toNat < corePlacedData1.length := by
    rw [corePlacedData1_length]; exact (bs.getD idx 0#8).isLt
  have hand64 := fu_multibyte_and64 (bs.getD idx 0#8)
  have hcut_9c : ∀ sm : State, sm.pc = sfuPl.base + 156#64 →
      FuLoopRegs s_entry sm p tbl ret bs.length idx →
      BitVec.truncate 32 (sm.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8) →
      sm.readReg64 (.gpr 14#5) = (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8).zeroExtend 64 →
      SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) sm
        (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
    intro sm hpc_m hregs_m hx13_m hx14_m
    have hrun_m := hregs_m.pres.running
    cases hw4_eq : (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8 == 4#8)
    · have hc4 : (BitVec.setWidth 32 (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8) == 4#32) = false := by
        rw [fu_byte32_beq _ 4#32 (by decide)]; exact hw4_eq
      cases hw3_eq : (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8 == 3#8)
      · have hc3 : (BitVec.setWidth 32 (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8) == 3#32) = false := by
          rw [fu_byte32_beq _ 3#32 (by decide)]; exact hw3_eq
        cases hw2_eq : (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8 == 2#8)
        · have hc2 : (BitVec.setWidth 32 (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8) != 2#32) = true := by
            rw [fu_byte32_bne _ 2#32 (by decide), show BitVec.ofNat 8 (2#32).toNat = 2#8 from rfl, hw2_eq]; rfl
          have hnot4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = false := by
            cases h : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8)
            · rfl
            · exact False.elim (Bool.noConfusion (hw4_eq.symm.trans (beq_iff_eq.mpr ((utf8CharWidth_eq_4_iff _).mpr h))))
          have hnot3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = false := by
            cases h : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8)
            · rfl
            · exact False.elim (Bool.noConfusion (hw3_eq.symm.trans (beq_iff_eq.mpr ((utf8CharWidth_eq_3_iff _).mpr h))))
          have hnot2 : (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = false := by
            cases h : (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8)
            · rfl
            · exact False.elim (Bool.noConfusion (hw2_eq.symm.trans (beq_iff_eq.mpr ((utf8CharWidth_eq_2_iff _).mpr h))))
          have herr := hval.trans (runUtf8ValidationLoop_err_lead hidx hnonAscii hnot2 hnot3 hnot4)
          apply rustSepWP_cut (mid := sfuPl.base + 560#64); wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact fuRetErr1RO_230 hpost herr rfl (fu_step_pres hregs_m.pres hrun_m)
            (by simp [arm64_norm, hregs_m.x8_eq]) (by simp [arm64_norm, hregs_m.x9_eq])
        · have hc2 : (BitVec.setWidth 32 (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8) != 2#32) = false := by
            rw [fu_byte32_bne _ 2#32 (by decide), show BitVec.ofNat 8 (2#32).toNat = 2#8 from rfl, hw2_eq]; rfl
          have hw2 : (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = true :=
            (utf8CharWidth_eq_2_iff _).mp (beq_iff_eq.mp hw2_eq)
          apply rustSepWP_cut (mid := sfuPl.base + 180#64); wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact fuWidth2RO hlen hpost hnext hidx hval hw2 rfl (fu_keep_regs hregs_m hrun_m)
      · have hc3 : (BitVec.setWidth 32 (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8) == 3#32) = true := by
          rw [fu_byte32_beq _ 3#32 (by decide)]; exact hw3_eq
        have hw3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = true :=
          (utf8CharWidth_eq_3_iff _).mp (beq_iff_eq.mp hw3_eq)
        apply rustSepWP_cut (mid := sfuPl.base + 208#64); wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
        exact fuWidth3RO hlen hpost hnext hidx hval hw3 rfl (fu_keep_regs hregs_m hrun_m) (by simpa only [arm64_norm] using hx13_m)
    · have hc4 : (BitVec.setWidth 32 (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8) == 4#32) = true := by
        rw [fu_byte32_beq _ 4#32 (by decide)]; exact hw4_eq
      have hw4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = true :=
        (utf8CharWidth_eq_4_iff _).mp (beq_iff_eq.mp hw4_eq)
      apply rustSepWP_cut (mid := sfuPl.base + 256#64); wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
      exact fuWidth4RO hlen hpost hnext hidx hval hw4 rfl (fu_keep_regs hregs_m hrun_m) (by simpa only [arm64_norm] using hx13_m)
  apply rustSepWP_cut (mid := sfuPl.base + 156#64)
  wp_conv_pre =>
    rw [fuWorkPreRO, ← sepConj_assoc, sepConj_comm (p ↦ᵣ bs) (tbl ↦ᵣ corePlacedData1),
        pointsToBytesRO_focus8 tbl corePlacedData1 (bs.getD idx 0#8).toNat hb0_lt]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  wp_conv_pre =>
    rw [← pointsToBytesRO_focus8 tbl corePlacedData1 (bs.getD idx 0#8).toNat hb0_lt,
        sepConj_comm (tbl ↦ᵣ corePlacedData1) (p ↦ᵣ bs), sepConj_assoc, ← fuWorkPreRO]
  refine hcut_9c _ rfl (fu_keep_regs hregs hrun) ?_ (by simp [arm64_norm])
  simp only [arm64_norm]; generalize bs.getD idx 0#8 = b0; revert b0; decide

/-! ## 4. ASCII Loops (`fuLoopCRO`, `fuAt70RO`, `fuLoopBRO`, `fuAt34RO`, `fuMainLoopRO`) -/

private theorem fuLoopCRO [SingleFromUtf8Pl] (rem : Nat) {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64) (hrem : bs.length - idx ≤ rem)
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextContRO s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length) (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hpc : s.pc = sfuPl.base + 120#64) (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  induction rem generalizing idx s with
  | zero => omega
  | succ rem ih =>
    have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
    by_cases hb0 : bs.getD idx 0#8 < 0x80#8
    · obtain ⟨htb64, htb32, htbse⟩ := fu_tbnz31_ascii hb0
      have hval1 := hval.trans (runUtf8ValidationLoop_step_ascii hidx hb0)
      have h9_1 : BitVec.ofNat 64 idx + 1#64 = BitVec.ofNat 64 (idx + 1) := bv64_ofNat_add_small idx 1
      by_cases h1 : idx + 1 < bs.length
      · have hne : (BitVec.ofNat 64 bs.length != BitVec.ofNat 64 (idx + 1)) = true := by
          rw [fu_bne_len (by omega) hlen]; simp [h1]
        apply rustSepWP_cut (mid := sfuPl.base + 120#64)
        wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs idx hidx]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← pointsToBytesRO_focus8 p bs idx hidx, ← fuWorkPreRO]
        refine ih (by omega) (hnext.mono (by omega)) h1 hval1 rfl
          ⟨fu_step_pres hregs.pres hrun, by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
            by simp [arm64_norm, hregs.x8_eq], by simp only [arm64_norm],
            by simp [arm64_norm, hregs.x10_eq], by simp [arm64_norm, hregs.x11_eq],
            by simp [arm64_norm, hregs.x12_eq]⟩
      · have heof : idx + 1 = bs.length := by omega
        have hne : (BitVec.ofNat 64 bs.length != BitVec.ofNat 64 (idx + 1)) = false := by
          rw [fu_bne_len (by omega) hlen]; simp [h1]
        have hok : runUtf8Validation bs = .ok () := by rw [hval1, drop_eq_nil_of_eq_len heof]; rfl
        apply rustSepWP_cut (mid := sfuPl.base + 524#64)
        wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs idx hidx]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← pointsToBytesRO_focus8 p bs idx hidx, ← fuWorkPreRO]
        exact fuRetOkRO hpost hok rfl (fu_step_pres hregs.pres hrun)
          (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hregs.x8_eq])
    · obtain ⟨htb64, htb32, htbse⟩ := fu_tbnz31_nonAscii hb0
      have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = false := fu_ule_false hidx hlen
      apply rustSepWP_cut (mid := sfuPl.base + 144#64)
      wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs idx hidx]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← pointsToBytesRO_focus8 p bs idx hidx, ← fuWorkPreRO]
      exact fuMultiByteRO hlen hpost hnext hidx hval hb0 rfl (fu_keep_regs hregs hrun) (by simp only [arm64_norm])

private theorem fuAt70RO [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop} (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextContRO s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hle : idx ≤ bs.length) (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hpc : s.pc = sfuPl.base + 112#64) (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
  by_cases hidx : idx < bs.length
  · have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = false := fu_ule_false hidx hlen
    apply rustSepWP_cut (mid := sfuPl.base + 120#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuLoopCRO (bs.length - idx) hlen (Nat.le_refl _) hpost hnext hidx hval rfl (fu_keep_regs hregs hrun)
  · have heof : idx = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = true := by rw [heof]; exact fu_ule_true
    have hok : runUtf8Validation bs = .ok () := by rw [hval, drop_eq_nil_of_eq_len heof]; rfl
    apply rustSepWP_cut (mid := sfuPl.base + 524#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetOkRO hpost hok rfl (fu_step_pres hregs.pres hrun)
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hregs.x8_eq])

private theorem fuLoopBRO [SingleFromUtf8Pl] (rem : Nat) {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64) (hrem : bs.length - idx ≤ rem)
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextContRO s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hle : idx ≤ bs.length) (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hpc : s.pc = sfuPl.base + 84#64) (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  induction rem generalizing idx s with
  | zero =>
    have hrun := hregs.pres.running; have hx9 := hregs.x9_eq; have hx10 := hregs.x10_eq
    have h16 : ¬ (idx + 16 ≤ bs.length) := by omega
    have hcs : (BitVec.ofNat 64 (bs.length - 15)).ule (BitVec.ofNat 64 idx) = true := by
      rw [fu_ule_sub15 hle hlen]; simp [h16]
    apply rustSepWP_cut (mid := sfuPl.base + 112#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuAt70RO hlen hpost hnext hle hval rfl (fu_keep_regs hregs hrun)
  | succ rem ih =>
    have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq; have hx10 := hregs.x10_eq
    by_cases h16 : idx + 16 ≤ bs.length
    · have hcs : (BitVec.ofNat 64 (bs.length - 15)).ule (BitVec.ofNat 64 idx) = false := by
        rw [fu_ule_sub15 hle hlen]; simp [h16]
      obtain ⟨w0, w1, hchunk, hfocus16⟩ := pointsToBytesRO_focus16_at p bs h16
      cases hswar : (((w1 ||| w0) &&& 0x8080808080808080#64) == 0#64)
      · apply rustSepWP_cut (mid := sfuPl.base + 112#64)
        wp_conv_pre => rw [fuWorkPreRO, hfocus16]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← hfocus16, ← fuWorkPreRO]
        exact fuAt70RO hlen hpost hnext hle hval rfl (fu_keep_regs hregs hrun)
      · have hval16 := hval.trans (runUtf8ValidationLoop_swar16 h16 hchunk (beq_iff_eq.mp hswar))
        have h9_16 : BitVec.ofNat 64 idx + 16#64 = BitVec.ofNat 64 (idx + 16) := bv64_ofNat_add_small idx 16
        apply rustSepWP_cut (mid := sfuPl.base + 84#64)
        wp_conv_pre => rw [fuWorkPreRO, hfocus16]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← hfocus16, ← fuWorkPreRO]
        refine ih (by omega) (hnext.mono (by omega)) (by omega) hval16 rfl
          ⟨fu_step_pres hregs.pres hrun, by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
            by simp [arm64_norm, hregs.x8_eq], by simp only [arm64_norm, hx9, h9_16],
            by simp [arm64_norm, hx10], by simp [arm64_norm, hregs.x11_eq],
            by simp [arm64_norm, hregs.x12_eq]⟩
    · have hcs : (BitVec.ofNat 64 (bs.length - 15)).ule (BitVec.ofNat 64 idx) = true := by
        rw [fu_ule_sub15 hle hlen]; simp [h16]
      apply rustSepWP_cut (mid := sfuPl.base + 112#64); wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      exact fuAt70RO hlen hpost hnext hle hval rfl (fu_keep_regs hregs hrun)

private theorem fuAt34RO [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop} (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextContRO s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length) (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hpc : s.pc = sfuPl.base + 52#64) (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq; have hx11 := hregs.x11_eq
  by_cases hb0 : bs.getD idx 0#8 < 0x80#8
  · obtain ⟨htb64, htb32, htbse⟩ := fu_tbnz31_ascii hb0
    let alignDiff : BitVec 64 :=
      BitVec.zeroExtend 64 (BitVec.truncate 32 (utf8AlignOff p) - BitVec.truncate 32 (BitVec.ofNat 64 idx))
    cases halign : ((alignDiff &&& 7#64) == 0#64)
    · have halign_f : ((BitVec.zeroExtend 64 (BitVec.truncate 32 (utf8AlignOff p) - BitVec.truncate 32 (BitVec.ofNat 64 idx)) &&& 7#64) == 0#64) = false := halign
      have hval1 := hval.trans (runUtf8ValidationLoop_step_ascii hidx hb0)
      have h9_1 : BitVec.ofNat 64 idx + 1#64 = BitVec.ofNat 64 (idx + 1) := bv64_ofNat_add_small idx 1
      apply rustSepWP_cut (mid := sfuPl.base + 44#64)
      wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs idx hidx]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← pointsToBytesRO_focus8 p bs idx hidx, ← fuWorkPreRO]
      refine hnext (idx + 1) _ (by omega) (by omega) hval1 rfl
        ⟨fu_step_pres hregs.pres hrun, by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
          by simp [arm64_norm, hregs.x8_eq], by simp only [arm64_norm, hx9, h9_1],
          by simp [arm64_norm, hregs.x10_eq], by simp [arm64_norm, hx11],
          by simp [arm64_norm, hregs.x12_eq]⟩
    · have halign_t : ((BitVec.zeroExtend 64 (BitVec.truncate 32 (utf8AlignOff p) - BitVec.truncate 32 (BitVec.ofNat 64 idx)) &&& 7#64) == 0#64) = true := halign
      apply rustSepWP_cut (mid := sfuPl.base + 84#64)
      wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs idx hidx]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← pointsToBytesRO_focus8 p bs idx hidx, ← fuWorkPreRO]
      exact fuLoopBRO (bs.length - idx) hlen (Nat.le_refl _) hpost hnext (by omega) hval rfl (fu_keep_regs hregs hrun)
  · obtain ⟨htb64, htb32, htbse⟩ := fu_tbnz31_nonAscii hb0
    apply rustSepWP_cut (mid := sfuPl.base + 144#64)
    wp_conv_pre => rw [fuWorkPreRO, pointsToBytesRO_focus8 p bs idx hidx]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    wp_conv_pre => rw [← pointsToBytesRO_focus8 p bs idx hidx, ← fuWorkPreRO]
    exact fuMultiByteRO hlen hpost hnext hidx hval hb0 rfl (fu_keep_regs hregs hrun) (by simp only [arm64_norm])

private theorem fuMainLoopRO [SingleFromUtf8Pl] (rem : Nat) {s_entry : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} (hlen : bs.length < 2 ^ 64) {post : State → SepProp → Prop}
    (hpost : FuPostContRO s_entry p tbl ret bs b18 b20 post)
    (idx : Nat) (s : State) (hle : idx ≤ bs.length) (hrem : bs.length - idx ≤ rem)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hpc : s.pc = sfuPl.base + 44#64) (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreRO p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  induction rem generalizing idx s with
  | zero =>
    have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
    have heof : idx = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = true := by rw [heof]; exact fu_ule_true
    have hok : runUtf8Validation bs = .ok () := by rw [hval, drop_eq_nil_of_eq_len heof]; rfl
    apply rustSepWP_cut (mid := sfuPl.base + 524#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetOkRO hpost hok rfl (fu_step_pres hregs.pres hrun)
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hregs.x8_eq])
  | succ rem ih =>
    have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
    by_cases hidx : idx < bs.length
    · have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = false := fu_ule_false hidx hlen
      have hnext : FuNextContRO s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post :=
        fun idx' sn hlt hle' hval' hpc' hregs' => ih idx' sn hle' (by omega) hval' hpc' hregs'
      apply rustSepWP_cut (mid := sfuPl.base + 52#64); wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      exact fuAt34RO hlen hpost hnext hidx hval rfl (fu_keep_regs hregs hrun)
    · have heof : idx = bs.length := by omega
      have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = true := by rw [heof]; exact fu_ule_true
      have hok : runUtf8Validation bs = .ok () := by rw [hval, drop_eq_nil_of_eq_len heof]; rfl
      apply rustSepWP_cut (mid := sfuPl.base + 524#64); wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      exact fuRetOkRO hpost hok rfl (fu_step_pres hregs.pres hrun)
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hregs.x8_eq])


/-! ## 5. Single-Block Raw RO Spec, Prologue, & `pureWordsProg` `subroutine_ok` -/

/-- Raw memory-independent single-block `coreFromUtf8ROSpec` (`p ↦ᵣ bs`), ready for
    `subroutine_ok_lift_pureWords_process`. -/
@[expose] def rawCoreFromUtf8ROSpec (tbl : BitVec 64) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 16 × BitVec 32) where
  pre := fun (p, ret, bs, b18, b20) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      s0.readReg64 .x8 = ret ∧ bs.length < 2 ^ 64⌝ ∗
      ((p ↦ᵣ bs) ∗ (tbl ↦ᵣ corePlacedData1)) ∗
      (memRegion ret 18 ∗ ((ret + 18#64) ↦₁₆ b18) ∗ ((ret + 20#64) ↦₃₂ b20))
  post := fun (p, ret, bs, b18, b20) _s0 _sf =>
    ((p ↦ᵣ bs) ∗ (tbl ↦ᵣ corePlacedData1)) ∗
      fromUtf8SretPost ret p bs.length b18 b20 (runUtf8Validation bs)

private theorem sfuBlock1RO_raw_ok [SingleFromUtf8Pl] :
    subroutine_ok (sfuPC.rebase sfuPl.base (fun _ => none)) sfuPl.base
      (rawCoreFromUtf8ROSpec (sfuPl.ρ coreUtf8CharWidthSym)) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨p, ret, bs, b18, b20⟩ R s0 hpc0 hrun0 hpre _hsp0
  let tbl := sfuPl.ρ coreUtf8CharWidthSym
  have htbl_eq : sfuPl.ρ coreUtf8CharWidthSym + 0#64 = tbl := by
    change tbl + 0#64 = tbl; bv_lin
  dsimp only [rawCoreFromUtf8ROSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0_0, hx1_0, hx8_0, hlen⟩, hpre⟩
  rw [memRegion18_eq ret] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨s17, s16, s_w8, s_w0, hpre⟩
  have hpre' : s0.mem ⊨ fuWorkPreRO p tbl ret bs s_w0 s_w8 s16 s17 b18 b20 ∗ R :=
    Satisfies.mono (by dsimp only [fuWorkPreRO]; sep_entail) hpre
  refine ⟨_, hpre', ?_⟩
  suffices hgo : ∀ (post : State → SepProp → Prop), FuPostContRO s0 p tbl ret bs b18 b20 post →
      SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s0.readReg64 .lr) s0
        (fuWorkPreRO p tbl ret bs s_w0 s_w8 s16 s17 b18 b20) post by
    refine hgo _ fun sf Q hpres_f _hpc_f hQ => ⟨fun hm_f => ?_, hpres_f.sp_eq, hpres_f.cs⟩
    exact Satisfies.mono
      (sepConj_mono_left (Entails.trans hQ (by dsimp only [fuPostPropRO]; sep_entail))) hm_f
  intro post hpost
  by_cases hempty : bs.length = 0
  · have hlen0 : BitVec.ofNat 64 bs.length = 0#64 := by simp [hempty]
    have hok : runUtf8Validation bs = .ok () := by
      cases bs with
      | nil => rfl
      | cons _ _ => simp at hempty
    apply rustSepWP_cut (mid := sfuPl.base + 524#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun0) ?_
    exact fuRetOkRO hpost hok rfl (fu_step_pres (FuPreserved.refl hrun0) hrun0)
      (by simp [arm64_norm, hx0_0]) (by simp [arm64_norm, hx1_0]) (by simp [arm64_norm, hx8_0])
  · have hpos : 0 < bs.length := Nat.pos_of_ne_zero hempty
    have hne0 : (BitVec.ofNat 64 bs.length == 0#64) = false := beq_false_of_ne fun heq => by
      have htn := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen] at htn; exact hempty htn
    have hnext0 : FuNextContRO s0 p tbl ret s_w0 s_w8 s16 s17 b18 b20 bs 0 post :=
      fun idx' sn _ hle' hval' hpc_n hregs_n =>
        fuMainLoopRO bs.length hlen hpost idx' sn hle' (by omega) hval' hpc_n hregs_n
    apply rustSepWP_cut (mid := sfuPl.base + 52#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun0) ?_
    refine fuAt34RO hlen hpost hnext0 hpos rfl rfl
      ⟨fu_step_pres (FuPreserved.refl hrun0) hrun0, by simp [arm64_norm, hx0_0],
        by simp [arm64_norm, hx1_0], by simp [arm64_norm, hx8_0], by simp [arm64_norm],
        by simpa [arm64_norm] using fu_sub15_csel hlen, by simp [arm64_norm, utf8AlignOff],
        by simpa [arm64_norm] using htbl_eq⟩

/-- Single-block `pureWordsProg` correctness of `core::str::converts::from_utf8` on read-only
    slices (`p ↦ᵣ bs`) under any single-block placement `hpl : fromUtf8Block.Placeable pl`. -/
theorem pureWordsProg_rawCoreFromUtf8RO_ok {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl) :
    subroutine_ok (pureWordsProg pl.base (fromUtf8PatchedWords pl)) pl.base
      (rawCoreFromUtf8ROSpec (pl.ρ coreUtf8CharWidthSym)) :=
  @subroutine_ok_pureWords_of_sfuRebase ⟨pl, hpl⟩ _ _ (@sfuBlock1RO_raw_ok ⟨pl, hpl⟩)

end

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlockRO
