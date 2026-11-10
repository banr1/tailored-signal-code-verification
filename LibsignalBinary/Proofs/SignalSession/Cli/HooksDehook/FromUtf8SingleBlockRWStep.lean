/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec.CoreFromUtf8
public import VerifiedLibraries.RustStd.Proofs.Wave2.FromUtf8Step
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Single-Block Return & Multi-Byte UTF-8 Stepping for `from_utf8` (`HooksDehook.FromUtf8SingleBlockRWStep`)

Single-block (`[SingleFromUtf8Pl]`) return-block and multi-byte UTF-8 sequence validation lemmas
(`sfuRetOk .. sfuMultiByte`) on `sfuPC.rebase sfuPl.base (fun _ => none)`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlockRWStep

open Arm64 Arm64.Obj Arm64.Process ProofLib
open ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open VerifiedLibraries.RustStd (FuLoopRegs FuPostCont FuPreserved bv64_ofNat_add_small
  corePlacedData1 corePlacedData1_length fromUtf8SretPost fuPostProp fuWorkPre fu_ule_false
  fu_ule_true isUtf8ContByte pointsToBytesRO_focus8 runUtf8Validation runUtf8ValidationLoop
  runUtf8ValidationLoop_err_lead runUtf8ValidationLoop_width2_eof
  runUtf8ValidationLoop_width2_step runUtf8ValidationLoop_width3_eof1
  runUtf8ValidationLoop_width3_eof2 runUtf8ValidationLoop_width3_err1
  runUtf8ValidationLoop_width3_step runUtf8ValidationLoop_width4_eof1
  runUtf8ValidationLoop_width4_eof2 runUtf8ValidationLoop_width4_eof3
  runUtf8ValidationLoop_width4_err1 runUtf8ValidationLoop_width4_err2
  runUtf8ValidationLoop_width4_step rustSepWP_cut signExtend32_and_ff64 sret_tail8_merge
  truncate32_signExtend64 utf8CharWidth_eq_2_iff utf8CharWidth_eq_3_iff
  utf8CharWidth_eq_4_iff utf8CharWidth_zeroExtend32_eq utf8ErrorLenAt utf8Width3Ok2
  utf8Width4Ok2)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock
  (SingleFromUtf8Pl sfuPl sfuPC
   fu_cmn41_le fu_cmn41_gt fu_cmn40_lt fu_cmn40_ge fu_cmn61_le fu_cmn71_le
   fu_byte32_beq fu_byte32_bne fu_e0_mask_eq fu_f0_sub_ult
   fu_e_ee_ef_ne_false fu_f_f1_f3_hi_false fu_multibyte_and64)

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


/-- `+0x20c .. +0x214` (`off = 524`): `stp x0, x1, [x8, #8]; str xzr, [x8]; ret` (`Ok(&str)`). -/
theorem sfuRetOk [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {post : State → SepProp → Prop}
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hok : runUtf8Validation bs = .ok ())
    (hpc : s.pc = sfuPl.base + 524#64)
    (hpres : FuPreserved s_entry s)
    (hx0 : s.readReg64 .x0 = p)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs.length)
    (hx8 : s.readReg64 .x8 = ret) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running
  have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPre, sret_tail8_merge ret s16 s17 b18 b20]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  refine hpost _ _ (fu_step_pres hpres hrun) rfl ?_
  dsimp only [fuPostProp]
  rw [hok]
  dsimp only [fromUtf8SretPost]
  sep_entail

/-- `+0x218 .. +0x22c` (`off = 536`): `Err { valid_up_to := idx, error_len := none }`. -/
private theorem sfuRetErrNone [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := none })
    (hpc : s.pc = sfuPl.base + 536#64)
    (hpres : FuPreserved s_entry s)
    (hx8 : s.readReg64 .x8 = ret)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running
  have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPre]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  refine hpost _ _ (fu_step_pres hpres hrun) rfl ?_
  dsimp only [fuPostProp]
  rw [herr]
  dsimp only [fromUtf8SretPost, utf8ErrorLenAt]
  have ha17 : (ret + 16#64) + 1#64 = ret + 17#64 := by bv_lin
  rw [ha17]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_right (BitVec.setWidth 8 (s.readReg64 (.gpr 13#5))) ?_
  sep_entail

/-- `+0x1f4 .. +0x208` (`off = 500`): `Err { valid_up_to := idx, error_len := some k }`
    given `w14[7:0] = 1#8` and `w13[7:0] = k`. -/
private theorem sfuRetErrSome_1f4 [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 k : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some k })
    (hpc : s.pc = sfuPl.base + 500#64)
    (hpres : FuPreserved s_entry s)
    (hx8 : s.readReg64 .x8 = ret)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx)
    (hx14 : BitVec.setWidth 8 (s.readReg64 (.gpr 14#5)) = 1#8)
    (hx13 : BitVec.setWidth 8 (s.readReg64 (.gpr 13#5)) = k) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running
  have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPre]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  refine hpost _ _ (fu_step_pres hpres hrun) rfl ?_
  dsimp only [fuPostProp]
  rw [herr]
  dsimp only [fromUtf8SretPost, utf8ErrorLenAt]
  have ha17 : (ret + 16#64) + 1#64 = ret + 17#64 := by bv_lin
  rw [ha17]
  sep_entail

/-- `+0x1ec .. +0x208` (`off = 492`): `Err { valid_up_to := idx, error_len := some 2#8 }`. -/
private theorem sfuRetErr2_1ec [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some 2#8 })
    (hpc : s.pc = sfuPl.base + 492#64)
    (hpres : FuPreserved s_entry s)
    (hx8 : s.readReg64 .x8 = ret)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running
  apply rustSepWP_cut (mid := sfuPl.base + 500#64)
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  exact sfuRetErrSome_1f4 hpost herr rfl (fu_step_pres hpres hrun)
    (by simp [arm64_norm, hx8]) (by simp [arm64_norm, hx9])
    (by simp [arm64_norm]) (by simp [arm64_norm])

/-- `+0x230 .. +0x24c` (`off = 560`): `Err { valid_up_to := idx, error_len := some 1#8 }`. -/
private theorem sfuRetErr1_230 [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some 1#8 })
    (hpc : s.pc = sfuPl.base + 560#64)
    (hpres : FuPreserved s_entry s)
    (hx8 : s.readReg64 .x8 = ret)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running
  have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPre]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  refine hpost _ _ (fu_step_pres hpres hrun) rfl ?_
  dsimp only [fuPostProp]
  rw [herr]
  dsimp only [fromUtf8SretPost, utf8ErrorLenAt]
  have ha17 : (ret + 16#64) + 1#64 = ret + 17#64 := by bv_lin
  rw [ha17]
  sep_entail

/-- `+0x250 .. +0x26c` (`off = 592`): `Err { valid_up_to := idx, error_len := some 3#8 }`. -/
private theorem sfuRetErr3_250 [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some 3#8 })
    (hpc : s.pc = sfuPl.base + 592#64)
    (hpres : FuPreserved s_entry s)
    (hx8 : s.readReg64 .x8 = ret)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running
  have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPre]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  refine hpost _ _ (fu_step_pres hpres hrun) rfl ?_
  dsimp only [fuPostProp]
  rw [herr]
  dsimp only [fromUtf8SretPost, utf8ErrorLenAt]
  have ha17 : (ret + 16#64) + 1#64 = ret + 17#64 := by bv_lin
  rw [ha17]
  sep_entail

abbrev SfuNextCont [SingleFromUtf8Pl] (s_entry : State)
    (p tbl ret s0 s8 : BitVec 64) (s16 s17 : BitVec 8) (b18 : BitVec 16) (b20 : BitVec 32)
    (bs : List (BitVec 8)) (idx : Nat) (post : State → SepProp → Prop) : Prop :=
  ∀ (idx' : Nat) (sn : State),
    idx < idx' → idx' ≤ bs.length →
    runUtf8Validation bs = runUtf8ValidationLoop idx' (bs.drop idx') →
    sn.pc = sfuPl.base + 44#64 →
    FuLoopRegs s_entry sn p tbl ret bs.length idx' →
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) sn
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post

/-- `+0xb4 .. +0xcc` (`off = 180`): 2-byte sequence (`0xC2 .. 0xDF`) validation. -/
private theorem sfuWidth2 [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : SfuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hw2 : (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = true)
    (hpc : s.pc = sfuPl.base + 180#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
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
      have hle_c : ConditionHolds .LE
          (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x41#32) = false := by
        rw [fu_cmn41_le]; exact hc1
      apply rustSepWP_cut (mid := sfuPl.base + 560#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 1) h1, ← hptr1]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr1, ← pointsToBytes_focus8 p bs (idx + 1) h1, ← fuWorkPre]
      exact sfuRetErr1_230 hpost herr rfl (fu_step_pres hregs.pres hrun)
        (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])
    · have hok2 : runUtf8Validation bs = runUtf8ValidationLoop (idx + 2) (bs.drop (idx + 2)) := by
        simpa only [hc1, ↓reduceIte] using hstep
      have hle_c : ConditionHolds .LE
          (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x41#32) = true := by
        rw [fu_cmn41_le]; exact hc1
      apply rustSepWP_cut (mid := sfuPl.base + 44#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 1) h1, ← hptr1]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr1, ← pointsToBytes_focus8 p bs (idx + 1) h1, ← fuWorkPre]
      refine hnext (idx + 2) _ (by omega) (by omega) hok2 rfl
        ⟨fu_step_pres hregs.pres hrun,
          by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
          by simp [arm64_norm, hregs.x8_eq], ?_,
          by simp [arm64_norm, hregs.x10_eq], by simp [arm64_norm, hregs.x11_eq],
          by simp [arm64_norm, hregs.x12_eq]⟩
      simpa only [arm64_norm] using bv64_ofNat_add_small idx 2
  · have heof : idx + 1 = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = true := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small, heof]
      exact fu_ule_true
    apply rustSepWP_cut (mid := sfuPl.base + 536#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact sfuRetErrNone hpost (hval.trans (runUtf8ValidationLoop_width2_eof hidx heof hw2)) rfl
      (fu_step_pres hregs.pres hrun) (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])

/-- `+0x1d4 .. +0x1e8` (`off = 468`): 3-byte sequence third-byte tail (`idx + 2`). -/
private theorem sfuWidth3Tail [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : SfuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx1 : idx + 1 < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hw3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = true)
    (hok2 : utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = true)
    (hpc : s.pc = sfuPl.base + 468#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
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
      have hle_c : ConditionHolds .LE
          (addsPState32 ((bs.getD (idx + 2) 0#8).signExtend 32) 0x41#32) = false := by
        rw [fu_cmn41_le]; exact hc2
      apply rustSepWP_cut (mid := sfuPl.base + 492#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 2) h2, ← hptr2]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr2, ← pointsToBytes_focus8 p bs (idx + 2) h2, ← fuWorkPre]
      exact sfuRetErr2_1ec hpost herr rfl (fu_step_pres hregs.pres hrun)
        (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])
    · have hok3 : runUtf8Validation bs = runUtf8ValidationLoop (idx + 3) (bs.drop (idx + 3)) := by
        simpa only [hc2, ↓reduceIte] using hstep
      have hle_c : ConditionHolds .LE
          (addsPState32 ((bs.getD (idx + 2) 0#8).signExtend 32) 0x41#32) = true := by
        rw [fu_cmn41_le]; exact hc2
      apply rustSepWP_cut (mid := sfuPl.base + 44#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 2) h2, ← hptr2]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr2, ← pointsToBytes_focus8 p bs (idx + 2) h2, ← fuWorkPre]
      refine hnext (idx + 3) _ (by omega) (by omega) hok3 rfl
        ⟨fu_step_pres hregs.pres hrun,
          by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
          by simp [arm64_norm, hregs.x8_eq], ?_,
          by simp [arm64_norm, hregs.x10_eq], by simp [arm64_norm, hregs.x11_eq],
          by simp [arm64_norm, hregs.x12_eq]⟩
      simpa only [arm64_norm] using bv64_ofNat_add_small idx 3
  · have heof2 : idx + 2 = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 2#64) = true := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small, heof2]
      exact fu_ule_true
    apply rustSepWP_cut (mid := sfuPl.base + 536#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact sfuRetErrNone hpost (hval.trans (runUtf8ValidationLoop_width3_eof2 hidx1 heof2 hw3 hok2)) rfl
      (fu_step_pres hregs.pres hrun) (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])

/-- `+0xd0 .. +0x1d0` (`off = 208`): 3-byte sequence (`0xE0 .. 0xEF`) second-byte dispatch. -/
private theorem sfuWidth3 [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : SfuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hw3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = true)
    (hpc : s.pc = sfuPl.base + 208#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx)
    (hx13 : BitVec.truncate 32 (s.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8)) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running
  have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq
  have hx9 := hregs.x9_eq
  by_cases h1 : idx + 1 < bs.length
  · have hptr1 : p + (BitVec.ofNat 64 idx + 1#64) = p + BitVec.ofNat 64 (idx + 1) := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = false := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
      exact fu_ule_false h1 hlen
    have hcut_e0 : ∀ sm : State,
        sm.pc = sfuPl.base + 224#64 →
        FuLoopRegs s_entry sm p tbl ret bs.length idx →
        BitVec.truncate 32 (sm.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8) →
        sm.readReg64 (.gpr 14#5) = (bs.getD (idx + 1) 0#8).zeroExtend 64 →
        SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) sm
          (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
      intro sm hpc_m hregs_m hx13_m hx14_m
      have hrun_m := hregs_m.pres.running
      cases hb0_e0 : (bs.getD idx 0#8 == 0xe0#8)
      · have heq_e0 : (BitVec.setWidth 32 (bs.getD idx 0#8) == 0xe0#32) = false := by
          rw [fu_byte32_beq _ 0xe0#32 (by decide)]; exact hb0_e0
        have hcut_ec : ∀ sn : State,
            sn.pc = sfuPl.base + 236#64 →
            FuLoopRegs s_entry sn p tbl ret bs.length idx →
            BitVec.truncate 32 (sn.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8) →
            BitVec.truncate 32 (sn.readReg64 (.gpr 14#5)) = (bs.getD (idx + 1) 0#8).signExtend 32 →
            SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) sn
              (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
          intro sn hpc_n hregs_n hx13_n hx14_n
          have hrun_n := hregs_n.pres.running
          cases hb0_ed : (bs.getD idx 0#8 == 0xed#8)
          · have hne_ed : (BitVec.setWidth 32 (bs.getD idx 0#8) != 0xed#32) = true := by
              rw [fu_byte32_bne _ 0xed#32 (by decide),
                  show BitVec.ofNat 8 (0xed#32).toNat = 0xed#8 from rfl, hb0_ed]
              rfl
            have hok2_eq : utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
                isUtf8ContByte (bs.getD (idx + 1) 0#8) := by
              simp only [utf8Width3Ok2, hb0_e0, hb0_ed, Bool.false_eq_true, ↓reduceIte]
            cases hcs_e1 : BitVec.ule 0x0c#32 (BitVec.setWidth 32 (bs.getD idx 0#8) - 0xe1#32)
            · cases hc1 : isUtf8ContByte (bs.getD (idx + 1) 0#8)
              · have hlt_c : ConditionHolds .LT
                    (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = false := by
                  rw [fu_cmn40_lt]; exact hc1
                have herr := hval.trans (runUtf8ValidationLoop_width3_err1 h1 hw3 (hok2_eq.trans hc1))
                apply rustSepWP_cut (mid := sfuPl.base + 560#64)
                wp_sym_steps
                refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
                exact sfuRetErr1_230 hpost herr rfl (fu_step_pres hregs_n.pres hrun_n)
                  (by simp [arm64_norm, hregs_n.x8_eq]) (by simp [arm64_norm, hregs_n.x9_eq])
              · have hlt_c : ConditionHolds .LT
                    (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = true := by
                  rw [fu_cmn40_lt]; exact hc1
                apply rustSepWP_cut (mid := sfuPl.base + 468#64)
                wp_sym_steps
                refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
                exact sfuWidth3Tail hlen hpost hnext h1 hval hw3 (hok2_eq.trans hc1) rfl
                  (fu_keep_regs hregs_n hrun_n)
            · have hne_ee := fu_e_ee_ef_ne_false (bs.getD idx 0#8) hw3 hb0_e0 hb0_ed hcs_e1
              cases hc1 : isUtf8ContByte (bs.getD (idx + 1) 0#8)
              · have hge_c : ConditionHolds .GE
                    (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = true := by
                  rw [fu_cmn40_ge, hc1]; rfl
                have herr := hval.trans (runUtf8ValidationLoop_width3_err1 h1 hw3 (hok2_eq.trans hc1))
                apply rustSepWP_cut (mid := sfuPl.base + 500#64)
                wp_sym_steps
                refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
                exact sfuRetErrSome_1f4 hpost herr rfl (fu_step_pres hregs_n.pres hrun_n)
                  (by simp [arm64_norm, hregs_n.x8_eq]) (by simp [arm64_norm, hregs_n.x9_eq])
                  (by simp [arm64_norm]) (by simp [arm64_norm])
              · have hge_c : ConditionHolds .GE
                    (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = false := by
                  rw [fu_cmn40_ge, hc1]; rfl
                apply rustSepWP_cut (mid := sfuPl.base + 468#64)
                wp_sym_steps
                refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
                exact sfuWidth3Tail hlen hpost hnext h1 hval hw3 (hok2_eq.trans hc1) rfl
                  (fu_keep_regs hregs_n hrun_n)
          · have hne_ed : (BitVec.setWidth 32 (bs.getD idx 0#8) != 0xed#32) = false := by
              rw [fu_byte32_bne _ 0xed#32 (by decide),
                  show BitVec.ofNat 8 (0xed#32).toNat = 0xed#8 from rfl, hb0_ed]
              rfl
            have hok2_eq : utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
                (0x80#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0x9f#8) := by
              simp only [utf8Width3Ok2, hb0_e0, hb0_ed, Bool.false_eq_true, ↓reduceIte]
            cases hed_ok : (0x80#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0x9f#8)
            · have hle_c : ConditionHolds .LE
                  (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x61#32) = false := by
                rw [fu_cmn61_le]; exact hed_ok
              have herr := hval.trans (runUtf8ValidationLoop_width3_err1 h1 hw3 (hok2_eq.trans hed_ok))
              apply rustSepWP_cut (mid := sfuPl.base + 560#64)
              wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact sfuRetErr1_230 hpost herr rfl (fu_step_pres hregs_n.pres hrun_n)
                (by simp [arm64_norm, hregs_n.x8_eq]) (by simp [arm64_norm, hregs_n.x9_eq])
            · have hle_c : ConditionHolds .LE
                  (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x61#32) = true := by
                rw [fu_cmn61_le]; exact hed_ok
              apply rustSepWP_cut (mid := sfuPl.base + 468#64)
              wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact sfuWidth3Tail hlen hpost hnext h1 hval hw3 (hok2_eq.trans hed_ok) rfl
                (fu_keep_regs hregs_n hrun_n)
        apply rustSepWP_cut (mid := sfuPl.base + 236#64)
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
        refine hcut_ec _ rfl (fu_keep_regs hregs_m hrun_m)
          (by simpa only [arm64_norm] using hx13_m) ?_
        simp only [arm64_norm]
        generalize bs.getD (idx + 1) 0#8 = b1; revert b1; decide
      · have heq_e0 : (BitVec.setWidth 32 (bs.getD idx 0#8) == 0xe0#32) = true := by
          rw [fu_byte32_beq _ 0xe0#32 (by decide)]; exact hb0_e0
        have hok2_eq : utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
            (0xa0#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0xbf#8) := by
          simp only [utf8Width3Ok2, hb0_e0, ↓reduceIte]
        cases he0_ok : (0xa0#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0xbf#8)
        · have hm_eq : ((BitVec.setWidth 32 (bs.getD (idx + 1) 0#8) &&& 0xe0#32) == 0xa0#32) = false := by
            rw [fu_e0_mask_eq]; exact he0_ok
          have herr := hval.trans (runUtf8ValidationLoop_width3_err1 h1 hw3 (hok2_eq.trans he0_ok))
          apply rustSepWP_cut (mid := sfuPl.base + 560#64)
          wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact sfuRetErr1_230 hpost herr rfl (fu_step_pres hregs_m.pres hrun_m)
            (by simp [arm64_norm, hregs_m.x8_eq]) (by simp [arm64_norm, hregs_m.x9_eq])
        · have hm_eq : ((BitVec.setWidth 32 (bs.getD (idx + 1) 0#8) &&& 0xe0#32) == 0xa0#32) = true := by
            rw [fu_e0_mask_eq]; exact he0_ok
          apply rustSepWP_cut (mid := sfuPl.base + 468#64)
          wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact sfuWidth3Tail hlen hpost hnext h1 hval hw3 (hok2_eq.trans he0_ok) rfl
            (fu_keep_regs hregs_m hrun_m)
    apply rustSepWP_cut (mid := sfuPl.base + 224#64)
    wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 1) h1, ← hptr1]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    wp_conv_pre => rw [hptr1, ← pointsToBytes_focus8 p bs (idx + 1) h1, ← fuWorkPre]
    exact hcut_e0 _ rfl (fu_keep_regs hregs hrun)
      (by simpa only [arm64_norm] using hx13) (by simp [arm64_norm])
  · have heof : idx + 1 = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = true := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small, heof]
      exact fu_ule_true
    apply rustSepWP_cut (mid := sfuPl.base + 536#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact sfuRetErrNone hpost (hval.trans (runUtf8ValidationLoop_width3_eof1 hidx heof hw3)) rfl
      (fu_step_pres hregs.pres hrun) (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])

/-- `+0x184 .. +0x1b4` (`off = 388`): 4-byte sequence third & fourth byte tail (`idx + 2`, `idx + 3`). -/
private theorem sfuWidth4Tail [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : SfuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx1 : idx + 1 < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hw4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = true)
    (hok2 : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = true)
    (hpc : s.pc = sfuPl.base + 388#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running
  have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq
  have hx9 := hregs.x9_eq
  by_cases h2 : idx + 2 < bs.length
  · have hptr2 : p + (BitVec.ofNat 64 idx + 2#64) = p + BitVec.ofNat 64 (idx + 2) := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small]
    have hcs2 : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 2#64) = false := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small]
      exact fu_ule_false h2 hlen
    have hse2 := truncate32_signExtend64 (bs.getD (idx + 2) 0#8)
    cases hc2 : isUtf8ContByte (bs.getD (idx + 2) 0#8)
    · have hgt_c : ConditionHolds .GT
          (addsPState32 ((bs.getD (idx + 2) 0#8).signExtend 32) 0x41#32) = true := by
        rw [fu_cmn41_gt, hc2]; rfl
      have herr := hval.trans (runUtf8ValidationLoop_width4_err2 h2 hw4 hok2 hc2)
      apply rustSepWP_cut (mid := sfuPl.base + 492#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 2) h2, ← hptr2]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr2, ← pointsToBytes_focus8 p bs (idx + 2) h2, ← fuWorkPre]
      exact sfuRetErr2_1ec hpost herr rfl (fu_step_pres hregs.pres hrun)
        (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])
    · have hgt_c : ConditionHolds .GT
          (addsPState32 ((bs.getD (idx + 2) 0#8).signExtend 32) 0x41#32) = false := by
        rw [fu_cmn41_gt, hc2]; rfl
      have hcut_19c : ∀ sm : State,
          sm.pc = sfuPl.base + 412#64 →
          FuLoopRegs s_entry sm p tbl ret bs.length idx →
          SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) sm
            (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
        intro sm hpc_m hregs_m
        have hrun_m := hregs_m.pres.running
        have hx0_m := hregs_m.x0_eq
        have hx1_m := hregs_m.x1_eq
        have hx9_m := hregs_m.x9_eq
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
            have hlt_c : ConditionHolds .LT
                (addsPState32 ((bs.getD (idx + 3) 0#8).signExtend 32) 0x40#32) = false := by
              rw [fu_cmn40_lt]; exact hc3
            apply rustSepWP_cut (mid := sfuPl.base + 592#64)
            wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 3) h3, ← hptr3]
            wp_sym_steps
            refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
            wp_conv_pre => rw [hptr3, ← pointsToBytes_focus8 p bs (idx + 3) h3, ← fuWorkPre]
            exact sfuRetErr3_250 hpost herr rfl (fu_step_pres hregs_m.pres hrun_m)
              (by simp [arm64_norm, hregs_m.x8_eq]) (by simp [arm64_norm, hx9_m])
          · have hok4 : runUtf8Validation bs = runUtf8ValidationLoop (idx + 4) (bs.drop (idx + 4)) := by
              simpa only [hc3, ↓reduceIte] using hstep
            have hlt_c : ConditionHolds .LT
                (addsPState32 ((bs.getD (idx + 3) 0#8).signExtend 32) 0x40#32) = true := by
              rw [fu_cmn40_lt]; exact hc3
            apply rustSepWP_cut (mid := sfuPl.base + 44#64)
            wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 3) h3, ← hptr3]
            wp_sym_steps
            refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
            wp_conv_pre => rw [hptr3, ← pointsToBytes_focus8 p bs (idx + 3) h3, ← fuWorkPre]
            refine hnext (idx + 4) _ (by omega) (by omega) hok4 rfl
              ⟨fu_step_pres hregs_m.pres hrun_m,
                by simp [arm64_norm, hx0_m], by simp [arm64_norm, hx1_m],
                by simp [arm64_norm, hregs_m.x8_eq], ?_,
                by simp [arm64_norm, hregs_m.x10_eq], by simp [arm64_norm, hregs_m.x11_eq],
                by simp [arm64_norm, hregs_m.x12_eq]⟩
            simpa only [arm64_norm] using bv64_ofNat_add_small idx 4
        · have heof3 : idx + 3 = bs.length := by omega
          have hcs3 : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 3#64) = true := by
            rw [show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, bv64_ofNat_add_small, heof3]
            exact fu_ule_true
          apply rustSepWP_cut (mid := sfuPl.base + 536#64)
          wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact sfuRetErrNone hpost (hval.trans (runUtf8ValidationLoop_width4_eof3 h2 heof3 hw4 hok2 hc2)) rfl
            (fu_step_pres hregs_m.pres hrun_m) (by simp [arm64_norm, hregs_m.x8_eq])
            (by simp [arm64_norm, hx9_m])
      apply rustSepWP_cut (mid := sfuPl.base + 412#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 2) h2, ← hptr2]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr2, ← pointsToBytes_focus8 p bs (idx + 2) h2, ← fuWorkPre]
      exact hcut_19c _ rfl (fu_keep_regs hregs hrun)
  · have heof2 : idx + 2 = bs.length := by omega
    have hcs2 : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 2#64) = true := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small, heof2]
      exact fu_ule_true
    apply rustSepWP_cut (mid := sfuPl.base + 536#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact sfuRetErrNone hpost (hval.trans (runUtf8ValidationLoop_width4_eof2 hidx1 heof2 hw4 hok2)) rfl
      (fu_step_pres hregs.pres hrun) (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])

/-- `+0x100 .. +0x180` (`off = 256`): 4-byte sequence (`0xF0 .. 0xF4`) second-byte dispatch. -/
private theorem sfuWidth4 [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : SfuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hw4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = true)
    (hpc : s.pc = sfuPl.base + 256#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx)
    (hx13 : BitVec.truncate 32 (s.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8)) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running
  have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq
  have hx9 := hregs.x9_eq
  by_cases h1 : idx + 1 < bs.length
  · have hptr1 : p + (BitVec.ofNat 64 idx + 1#64) = p + BitVec.ofNat 64 (idx + 1) := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = false := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
      exact fu_ule_false h1 hlen
    have hcut_110 : ∀ sm : State,
        sm.pc = sfuPl.base + 272#64 →
        FuLoopRegs s_entry sm p tbl ret bs.length idx →
        BitVec.truncate 32 (sm.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8) →
        sm.readReg64 (.gpr 14#5) = (bs.getD (idx + 1) 0#8).zeroExtend 64 →
        SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) sm
          (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
      intro sm hpc_m hregs_m hx13_m hx14_m
      have hrun_m := hregs_m.pres.running
      cases hb0_f0 : (bs.getD idx 0#8 == 0xf0#8)
      · have heq_f0 : (BitVec.setWidth 32 (bs.getD idx 0#8) == 0xf0#32) = false := by
          rw [fu_byte32_beq _ 0xf0#32 (by decide)]; exact hb0_f0
        have hcut_11c : ∀ sn : State,
            sn.pc = sfuPl.base + 284#64 →
            FuLoopRegs s_entry sn p tbl ret bs.length idx →
            BitVec.truncate 32 (sn.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8) →
            BitVec.truncate 32 (sn.readReg64 (.gpr 14#5)) = (bs.getD (idx + 1) 0#8).signExtend 32 →
            SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) sn
              (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
          intro sn hpc_n hregs_n hx13_n hx14_n
          have hrun_n := hregs_n.pres.running
          cases hb0_f4 : (bs.getD idx 0#8 == 0xf4#8)
          · have hne_f4 : (BitVec.setWidth 32 (bs.getD idx 0#8) != 0xf4#32) = true := by
              rw [fu_byte32_bne _ 0xf4#32 (by decide),
                  show BitVec.ofNat 8 (0xf4#32).toNat = 0xf4#8 from rfl, hb0_f4]
              rfl
            have hhi_false := fu_f_f1_f3_hi_false (bs.getD idx 0#8) hw4 hb0_f0 hb0_f4
            have hok2_eq : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
                isUtf8ContByte (bs.getD (idx + 1) 0#8) := by
              simp only [utf8Width4Ok2, hb0_f0, hb0_f4, Bool.false_eq_true, ↓reduceIte]
            cases hc1 : isUtf8ContByte (bs.getD (idx + 1) 0#8)
            · have hge_c : ConditionHolds .GE
                  (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = true := by
                rw [fu_cmn40_ge, hc1]; rfl
              have herr := hval.trans (runUtf8ValidationLoop_width4_err1 h1 hw4 (hok2_eq.trans hc1))
              apply rustSepWP_cut (mid := sfuPl.base + 500#64)
              wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact sfuRetErrSome_1f4 hpost herr rfl (fu_step_pres hregs_n.pres hrun_n)
                (by simp [arm64_norm, hregs_n.x8_eq]) (by simp [arm64_norm, hregs_n.x9_eq])
                (by simp [arm64_norm]) (by simp [arm64_norm])
            · have hge_c : ConditionHolds .GE
                  (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = false := by
                rw [fu_cmn40_ge, hc1]; rfl
              apply rustSepWP_cut (mid := sfuPl.base + 388#64)
              wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact sfuWidth4Tail hlen hpost hnext h1 hval hw4 (hok2_eq.trans hc1) rfl
                (fu_keep_regs hregs_n hrun_n)
          · have hne_f4 : (BitVec.setWidth 32 (bs.getD idx 0#8) != 0xf4#32) = false := by
              rw [fu_byte32_bne _ 0xf4#32 (by decide),
                  show BitVec.ofNat 8 (0xf4#32).toNat = 0xf4#8 from rfl, hb0_f4]
              rfl
            have hok2_eq : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
                (0x80#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0x8f#8) := by
              simp only [utf8Width4Ok2, hb0_f0, hb0_f4, Bool.false_eq_true, ↓reduceIte]
            cases hf4_ok : (0x80#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0x8f#8)
            · have hle_c : ConditionHolds .LE
                  (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x71#32) = false := by
                rw [fu_cmn71_le]; exact hf4_ok
              have herr := hval.trans (runUtf8ValidationLoop_width4_err1 h1 hw4 (hok2_eq.trans hf4_ok))
              apply rustSepWP_cut (mid := sfuPl.base + 560#64)
              wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact sfuRetErr1_230 hpost herr rfl (fu_step_pres hregs_n.pres hrun_n)
                (by simp [arm64_norm, hregs_n.x8_eq]) (by simp [arm64_norm, hregs_n.x9_eq])
            · have hle_c : ConditionHolds .LE
                  (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x71#32) = true := by
                rw [fu_cmn71_le]; exact hf4_ok
              apply rustSepWP_cut (mid := sfuPl.base + 388#64)
              wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact sfuWidth4Tail hlen hpost hnext h1 hval hw4 (hok2_eq.trans hf4_ok) rfl
                (fu_keep_regs hregs_n hrun_n)
        apply rustSepWP_cut (mid := sfuPl.base + 284#64)
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
        refine hcut_11c _ rfl (fu_keep_regs hregs_m hrun_m)
          (by simpa only [arm64_norm] using hx13_m) ?_
        simp only [arm64_norm]
        generalize bs.getD (idx + 1) 0#8 = b1; revert b1; decide
      · have heq_f0 : (BitVec.setWidth 32 (bs.getD idx 0#8) == 0xf0#32) = true := by
          rw [fu_byte32_beq _ 0xf0#32 (by decide)]; exact hb0_f0
        have hok2_eq : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
            (0x90#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0xbf#8) := by
          simp only [utf8Width4Ok2, hb0_f0, ↓reduceIte]
        cases hf0_ok : (0x90#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0xbf#8)
        · have hcc : BitVec.ult (BitVec.setWidth 32 (bs.getD (idx + 1) 0#8) - 0x90#32) 0x30#32 = false := by
            rw [fu_f0_sub_ult]; exact hf0_ok
          have herr := hval.trans (runUtf8ValidationLoop_width4_err1 h1 hw4 (hok2_eq.trans hf0_ok))
          apply rustSepWP_cut (mid := sfuPl.base + 560#64)
          wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact sfuRetErr1_230 hpost herr rfl (fu_step_pres hregs_m.pres hrun_m)
            (by simp [arm64_norm, hregs_m.x8_eq]) (by simp [arm64_norm, hregs_m.x9_eq])
        · have hcc : BitVec.ult (BitVec.setWidth 32 (bs.getD (idx + 1) 0#8) - 0x90#32) 0x30#32 = true := by
            rw [fu_f0_sub_ult]; exact hf0_ok
          apply rustSepWP_cut (mid := sfuPl.base + 388#64)
          wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact sfuWidth4Tail hlen hpost hnext h1 hval hw4 (hok2_eq.trans hf0_ok) rfl
            (fu_keep_regs hregs_m hrun_m)
    apply rustSepWP_cut (mid := sfuPl.base + 272#64)
    wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 1) h1, ← hptr1]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    wp_conv_pre => rw [hptr1, ← pointsToBytes_focus8 p bs (idx + 1) h1, ← fuWorkPre]
    exact hcut_110 _ rfl (fu_keep_regs hregs hrun)
      (by simpa only [arm64_norm] using hx13) (by simp [arm64_norm])
  · have heof : idx + 1 = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = true := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small, heof]
      exact fu_ule_true
    apply rustSepWP_cut (mid := sfuPl.base + 536#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact sfuRetErrNone hpost (hval.trans (runUtf8ValidationLoop_width4_eof1 hidx heof hw4)) rfl
      (fu_step_pres hregs.pres hrun) (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])

/-- `+0x90 .. +0xb0` (`off = 144`): `UTF8_CHAR_WIDTH` table lookup (`corePlacedData1`) & width dispatch. -/
theorem sfuMultiByte [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : SfuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hnonAscii : ¬ (bs.getD idx 0#8 < 0x80#8))
    (hpc : s.pc = sfuPl.base + 144#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx)
    (hx13 : s.readReg64 (.gpr 13#5) =
      BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (bs.getD idx 0#8)))) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running
  have hx12 := hregs.x12_eq
  have hb0_lt : (bs.getD idx 0#8).toNat < corePlacedData1.length := by
    rw [corePlacedData1_length]; exact (bs.getD idx 0#8).isLt
  have hand64 := fu_multibyte_and64 (bs.getD idx 0#8)
  have hcut_9c : ∀ sm : State,
      sm.pc = sfuPl.base + 156#64 →
      FuLoopRegs s_entry sm p tbl ret bs.length idx →
      BitVec.truncate 32 (sm.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8) →
      sm.readReg64 (.gpr 14#5) = (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8).zeroExtend 64 →
      SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) sm
        (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
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
            rw [fu_byte32_bne _ 2#32 (by decide),
                show BitVec.ofNat 8 (2#32).toNat = 2#8 from rfl, hw2_eq]
            rfl
          have hnot4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = false := by
            cases h : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8)
            · rfl
            · exact False.elim (Bool.noConfusion
                (hw4_eq.symm.trans (beq_iff_eq.mpr ((utf8CharWidth_eq_4_iff _).mpr h))))
          have hnot3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = false := by
            cases h : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8)
            · rfl
            · exact False.elim (Bool.noConfusion
                (hw3_eq.symm.trans (beq_iff_eq.mpr ((utf8CharWidth_eq_3_iff _).mpr h))))
          have hnot2 : (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = false := by
            cases h : (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8)
            · rfl
            · exact False.elim (Bool.noConfusion
                (hw2_eq.symm.trans (beq_iff_eq.mpr ((utf8CharWidth_eq_2_iff _).mpr h))))
          have herr := hval.trans (runUtf8ValidationLoop_err_lead hidx hnonAscii hnot2 hnot3 hnot4)
          apply rustSepWP_cut (mid := sfuPl.base + 560#64)
          wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact sfuRetErr1_230 hpost herr rfl (fu_step_pres hregs_m.pres hrun_m)
            (by simp [arm64_norm, hregs_m.x8_eq]) (by simp [arm64_norm, hregs_m.x9_eq])
        · have hc2 : (BitVec.setWidth 32 (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8) != 2#32) = false := by
            rw [fu_byte32_bne _ 2#32 (by decide),
                show BitVec.ofNat 8 (2#32).toNat = 2#8 from rfl, hw2_eq]
            rfl
          have hw2 : (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = true :=
            (utf8CharWidth_eq_2_iff _).mp (beq_iff_eq.mp hw2_eq)
          apply rustSepWP_cut (mid := sfuPl.base + 180#64)
          wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact sfuWidth2 hlen hpost hnext hidx hval hw2 rfl (fu_keep_regs hregs_m hrun_m)
      · have hc3 : (BitVec.setWidth 32 (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8) == 3#32) = true := by
          rw [fu_byte32_beq _ 3#32 (by decide)]; exact hw3_eq
        have hw3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = true :=
          (utf8CharWidth_eq_3_iff _).mp (beq_iff_eq.mp hw3_eq)
        apply rustSepWP_cut (mid := sfuPl.base + 208#64)
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
        exact sfuWidth3 hlen hpost hnext hidx hval hw3 rfl (fu_keep_regs hregs_m hrun_m)
          (by simpa only [arm64_norm] using hx13_m)
    · have hc4 : (BitVec.setWidth 32 (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8) == 4#32) = true := by
        rw [fu_byte32_beq _ 4#32 (by decide)]; exact hw4_eq
      have hw4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = true :=
        (utf8CharWidth_eq_4_iff _).mp (beq_iff_eq.mp hw4_eq)
      apply rustSepWP_cut (mid := sfuPl.base + 256#64)
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
      exact sfuWidth4 hlen hpost hnext hidx hval hw4 rfl (fu_keep_regs hregs_m hrun_m)
        (by simpa only [arm64_norm] using hx13_m)
  apply rustSepWP_cut (mid := sfuPl.base + 156#64)
  wp_conv_pre =>
    rw [fuWorkPre, ← sepConj_assoc, sepConj_comm (p ↦ₛ bs) (tbl ↦ᵣ corePlacedData1),
        pointsToBytesRO_focus8 tbl corePlacedData1 (bs.getD idx 0#8).toNat hb0_lt]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  wp_conv_pre =>
    rw [← pointsToBytesRO_focus8 tbl corePlacedData1 (bs.getD idx 0#8).toNat hb0_lt,
        sepConj_comm (tbl ↦ᵣ corePlacedData1) (p ↦ₛ bs), sepConj_assoc, ← fuWorkPre]
  refine hcut_9c _ rfl (fu_keep_regs hregs hrun) ?_ (by simp [arm64_norm])
  simp only [arm64_norm]
  generalize bs.getD idx 0#8 = b0; revert b0; decide

end

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlockRWStep
