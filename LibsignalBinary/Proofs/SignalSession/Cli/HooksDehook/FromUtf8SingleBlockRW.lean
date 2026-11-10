/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec.CoreFromUtf8
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlockRWStep
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Single-Block Read-Write Slice Stepping for `from_utf8` (`HooksDehook.FromUtf8SingleBlockRW`)

Proves `pureWordsProg_rawCoreFromUtf8_ok` directly over the `156`-word single-block placement
`fromUtf8Block.Placeable pl` (`0` dependency on other blocks of `coreMultiLib`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlockRW

open Arm64 Arm64.Obj Arm64.Process ProofLib
open ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open VerifiedLibraries.RustStd (FuLoopRegs FuPostCont FuPreserved bv64_ofNat_add_small
  coreFromUtf8Spec coreFromUtf8_ok coreFromUtf8_subroutineOk corePlacedData1
  coreUtf8CharWidthSym drop_eq_nil_of_eq_len fromUtf8SretPost fuPostProp fuWorkPre
  fu_ule_false fu_ule_true memRegion18_eq pointsToBytes_focus16_at runUtf8Validation
  runUtf8ValidationLoop runUtf8ValidationLoop_step_ascii runUtf8ValidationLoop_swar16
  rustSepWP_cut utf8AlignOff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock
  (fromUtf8Block fromUtf8PatchedWords SingleFromUtf8Pl sfuPl sfuPC
   subroutine_ok_pureWords_of_sfuRebase
   fu_tbnz31_64 fu_tbnz31_32 fu_tbnz31_se fu_bne_len fu_ule_sub15 fu_sub15_csel)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlockRWStep (SfuNextCont
  sfuMultiByte sfuRetOk)

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

/-! ## 1. ASCII Loops (`fuLoopC`, `fuAt70`, `fuLoopB`, `fuAt34`, `fuMainLoop`) -/

private theorem sfuNextCont_mono [SingleFromUtf8Pl] {s_entry : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx idx1 : Nat} {post : State → SepProp → Prop}
    (hle : idx ≤ idx1)
    (h : SfuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post) :
    SfuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx1 post :=
  fun idx' sn hlt => h idx' sn (by omega)

/-- `+0x78 .. +0x8c` (`off = 120`): post-SWAR byte-by-byte ASCII scan Loop C. -/
private theorem fuLoopC [SingleFromUtf8Pl]
    (rem : Nat) {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hrem : bs.length - idx ≤ rem)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : SfuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hpc : s.pc = sfuPl.base + 120#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  induction rem generalizing idx s with
  | zero => omega
  | succ rem ih =>
    have hrun := hregs.pres.running
    have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq
    have hx9 := hregs.x9_eq
    by_cases hb0 : bs.getD idx 0#8 < 0x80#8
    · have htb64 : (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (bs.getD idx 0#8)))).getLsbD 31 = false := by
        rw [fu_tbnz31_64, decide_eq_true hb0]; rfl
      have htb32 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (bs.getD idx 0#8))))).getLsbD 31 = false := by
        rw [fu_tbnz31_32, decide_eq_true hb0]; rfl
      have htbse : ((bs.getD idx 0#8).signExtend 32).getLsbD 31 = false := by
        rw [fu_tbnz31_se, decide_eq_true hb0]; rfl
      have hval1 := hval.trans (runUtf8ValidationLoop_step_ascii hidx hb0)
      have h9_1 : BitVec.ofNat 64 idx + 1#64 = BitVec.ofNat 64 (idx + 1) :=
        bv64_ofNat_add_small idx 1
      by_cases h1 : idx + 1 < bs.length
      · have hne : (BitVec.ofNat 64 bs.length != BitVec.ofNat 64 (idx + 1)) = true := by
          rw [fu_bne_len (by omega) hlen]; simp [h1]
        apply rustSepWP_cut (mid := sfuPl.base + 120#64)
        wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs idx hidx]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← pointsToBytes_focus8 p bs idx hidx, ← fuWorkPre]
        refine ih (by omega) (sfuNextCont_mono (by omega) hnext) h1 hval1 rfl
          ⟨fu_step_pres hregs.pres hrun,
            by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
            by simp [arm64_norm, hregs.x8_eq], ?_,
            by simp [arm64_norm, hregs.x10_eq], by simp [arm64_norm, hregs.x11_eq],
            by simp [arm64_norm, hregs.x12_eq]⟩
        simp only [arm64_norm]
      · have heof : idx + 1 = bs.length := by omega
        have hne : (BitVec.ofNat 64 bs.length != BitVec.ofNat 64 (idx + 1)) = false := by
          rw [fu_bne_len (by omega) hlen]; simp [h1]
        have hok : runUtf8Validation bs = .ok () := by
          rw [hval1, drop_eq_nil_of_eq_len heof]; rfl
        apply rustSepWP_cut (mid := sfuPl.base + 524#64)
        wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs idx hidx]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← pointsToBytes_focus8 p bs idx hidx, ← fuWorkPre]
        exact sfuRetOk hpost hok rfl (fu_step_pres hregs.pres hrun)
          (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1])
          (by simp [arm64_norm, hregs.x8_eq])
    · have htb64 : (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (bs.getD idx 0#8)))).getLsbD 31 = true := by
        rw [fu_tbnz31_64, decide_eq_false hb0]; rfl
      have htb32 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (bs.getD idx 0#8))))).getLsbD 31 = true := by
        rw [fu_tbnz31_32, decide_eq_false hb0]; rfl
      have htbse : ((bs.getD idx 0#8).signExtend 32).getLsbD 31 = true := by
        rw [fu_tbnz31_se, decide_eq_false hb0]; rfl
      have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = false :=
        fu_ule_false hidx hlen
      apply rustSepWP_cut (mid := sfuPl.base + 144#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs idx hidx]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← pointsToBytes_focus8 p bs idx hidx, ← fuWorkPre]
      refine sfuMultiByte hlen hpost hnext hidx hval hb0 rfl (fu_keep_regs hregs hrun) ?_
      simp only [arm64_norm]

/-- `+0x70 .. +0x74` (`off = 112`): post-SWAR end-check before Loop C. -/
private theorem fuAt70 [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : SfuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hle : idx ≤ bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hpc : s.pc = sfuPl.base + 112#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running
  have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq
  have hx9 := hregs.x9_eq
  by_cases hidx : idx < bs.length
  · have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = false :=
      fu_ule_false hidx hlen
    apply rustSepWP_cut (mid := sfuPl.base + 120#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuLoopC (bs.length - idx) hlen (Nat.le_refl _) hpost hnext hidx hval rfl
      (fu_keep_regs hregs hrun)
  · have heof : idx = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = true := by
      rw [heof]; exact fu_ule_true
    have hok : runUtf8Validation bs = .ok () := by
      rw [hval, drop_eq_nil_of_eq_len heof]; rfl
    apply rustSepWP_cut (mid := sfuPl.base + 524#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact sfuRetOk hpost hok rfl (fu_step_pres hregs.pres hrun)
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1])
      (by simp [arm64_norm, hregs.x8_eq])

/-- `+0x54 .. +0x6c` (`off = 84`, back-edge `+0x50`): SWAR 16-byte ASCII Loop B. -/
private theorem fuLoopB [SingleFromUtf8Pl]
    (rem : Nat) {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hrem : bs.length - idx ≤ rem)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : SfuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hle : idx ≤ bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hpc : s.pc = sfuPl.base + 84#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  induction rem generalizing idx s with
  | zero =>
    have hrun := hregs.pres.running
    have hx9 := hregs.x9_eq
    have hx10 := hregs.x10_eq
    have h16 : ¬ (idx + 16 ≤ bs.length) := by omega
    have hcs : (BitVec.ofNat 64 (bs.length - 15)).ule (BitVec.ofNat 64 idx) = true := by
      rw [fu_ule_sub15 hle hlen]; simp [h16]
    apply rustSepWP_cut (mid := sfuPl.base + 112#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuAt70 hlen hpost hnext hle hval rfl (fu_keep_regs hregs hrun)
  | succ rem ih =>
    have hrun := hregs.pres.running
    have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq
    have hx9 := hregs.x9_eq
    have hx10 := hregs.x10_eq
    by_cases h16 : idx + 16 ≤ bs.length
    · have hcs : (BitVec.ofNat 64 (bs.length - 15)).ule (BitVec.ofNat 64 idx) = false := by
        rw [fu_ule_sub15 hle hlen]; simp [h16]
      obtain ⟨w0, w1, hchunk, hfocus16⟩ := pointsToBytes_focus16_at p bs h16
      cases hswar : (((w1 ||| w0) &&& 0x8080808080808080#64) == 0#64)
      · apply rustSepWP_cut (mid := sfuPl.base + 112#64)
        wp_conv_pre => rw [fuWorkPre, hfocus16]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← hfocus16, ← fuWorkPre]
        exact fuAt70 hlen hpost hnext hle hval rfl (fu_keep_regs hregs hrun)
      · have hval16 := hval.trans (runUtf8ValidationLoop_swar16 h16 hchunk (beq_iff_eq.mp hswar))
        have h9_16 : BitVec.ofNat 64 idx + 16#64 = BitVec.ofNat 64 (idx + 16) :=
          bv64_ofNat_add_small idx 16
        apply rustSepWP_cut (mid := sfuPl.base + 84#64)
        wp_conv_pre => rw [fuWorkPre, hfocus16]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← hfocus16, ← fuWorkPre]
        refine ih (by omega) (sfuNextCont_mono (by omega) hnext) (by omega) hval16 rfl
          ⟨fu_step_pres hregs.pres hrun,
            by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
            by simp [arm64_norm, hregs.x8_eq], ?_,
            by simp [arm64_norm, hx10], by simp [arm64_norm, hregs.x11_eq],
            by simp [arm64_norm, hregs.x12_eq]⟩
        simp only [arm64_norm, hx9, h9_16]
    · have hcs : (BitVec.ofNat 64 (bs.length - 15)).ule (BitVec.ofNat 64 idx) = true := by
        rw [fu_ule_sub15 hle hlen]; simp [h16]
      apply rustSepWP_cut (mid := sfuPl.base + 112#64)
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      exact fuAt70 hlen hpost hnext hle hval rfl (fu_keep_regs hregs hrun)

/-- `+0x34 .. +0x4c` (`off = 52`): lead-byte test & 8-byte alignment check. -/
private theorem fuAt34 [SingleFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : SfuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hpc : s.pc = sfuPl.base + 52#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running
  have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq
  have hx9 := hregs.x9_eq
  have hx11 := hregs.x11_eq
  by_cases hb0 : bs.getD idx 0#8 < 0x80#8
  · have htb64 : (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (bs.getD idx 0#8)))).getLsbD 31 = false := by
      rw [fu_tbnz31_64, decide_eq_true hb0]; rfl
    have htb32 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (bs.getD idx 0#8))))).getLsbD 31 = false := by
      rw [fu_tbnz31_32, decide_eq_true hb0]; rfl
    have htbse : ((bs.getD idx 0#8).signExtend 32).getLsbD 31 = false := by
      rw [fu_tbnz31_se, decide_eq_true hb0]; rfl
    let alignDiff : BitVec 64 :=
      BitVec.zeroExtend 64 (BitVec.truncate 32 (utf8AlignOff p) - BitVec.truncate 32 (BitVec.ofNat 64 idx))
    cases halign : ((alignDiff &&& 7#64) == 0#64)
    · have halign_f : ((BitVec.zeroExtend 64 (BitVec.truncate 32 (utf8AlignOff p) - BitVec.truncate 32 (BitVec.ofNat 64 idx)) &&& 7#64) == 0#64) = false := halign
      have hval1 := hval.trans (runUtf8ValidationLoop_step_ascii hidx hb0)
      have h9_1 : BitVec.ofNat 64 idx + 1#64 = BitVec.ofNat 64 (idx + 1) :=
        bv64_ofNat_add_small idx 1
      apply rustSepWP_cut (mid := sfuPl.base + 44#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs idx hidx]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← pointsToBytes_focus8 p bs idx hidx, ← fuWorkPre]
      refine hnext (idx + 1) _ (by omega) (by omega) hval1 rfl
        ⟨fu_step_pres hregs.pres hrun,
          by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
          by simp [arm64_norm, hregs.x8_eq], ?_,
          by simp [arm64_norm, hregs.x10_eq], by simp [arm64_norm, hx11],
          by simp [arm64_norm, hregs.x12_eq]⟩
      simp only [arm64_norm, hx9, h9_1]
    · have halign_t : ((BitVec.zeroExtend 64 (BitVec.truncate 32 (utf8AlignOff p) - BitVec.truncate 32 (BitVec.ofNat 64 idx)) &&& 7#64) == 0#64) = true := halign
      apply rustSepWP_cut (mid := sfuPl.base + 84#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs idx hidx]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← pointsToBytes_focus8 p bs idx hidx, ← fuWorkPre]
      exact fuLoopB (bs.length - idx) hlen (Nat.le_refl _) hpost hnext (by omega) hval rfl
        (fu_keep_regs hregs hrun)
  · have htb64 : (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (bs.getD idx 0#8)))).getLsbD 31 = true := by
      rw [fu_tbnz31_64, decide_eq_false hb0]; rfl
    have htb32 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (bs.getD idx 0#8))))).getLsbD 31 = true := by
      rw [fu_tbnz31_32, decide_eq_false hb0]; rfl
    have htbse : ((bs.getD idx 0#8).signExtend 32).getLsbD 31 = true := by
      rw [fu_tbnz31_se, decide_eq_false hb0]; rfl
    apply rustSepWP_cut (mid := sfuPl.base + 144#64)
    wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs idx hidx]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    wp_conv_pre => rw [← pointsToBytes_focus8 p bs idx hidx, ← fuWorkPre]
    refine sfuMultiByte hlen hpost hnext hidx hval hb0 rfl (fu_keep_regs hregs hrun) ?_
    simp only [arm64_norm]

/-- `+0x2c .. +0x30` (`off = 44`): main validation loop header (`subs xzr, x9, x1; b.cs +0x20c`). -/
private theorem fuMainLoop [SingleFromUtf8Pl]
    (rem : Nat) {s_entry : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)}
    (hlen : bs.length < 2 ^ 64)
    {post : State → SepProp → Prop}
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (idx : Nat) (s : State)
    (hle : idx ≤ bs.length)
    (hrem : bs.length - idx ≤ rem)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hpc : s.pc = sfuPl.base + 44#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  induction rem generalizing idx s with
  | zero =>
    have hrun := hregs.pres.running
    have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq
    have hx9 := hregs.x9_eq
    have heof : idx = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = true := by
      rw [heof]; exact fu_ule_true
    have hok : runUtf8Validation bs = .ok () := by
      rw [hval, drop_eq_nil_of_eq_len heof]; rfl
    apply rustSepWP_cut (mid := sfuPl.base + 524#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact sfuRetOk hpost hok rfl (fu_step_pres hregs.pres hrun)
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1])
      (by simp [arm64_norm, hregs.x8_eq])
  | succ rem ih =>
    have hrun := hregs.pres.running
    have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq
    have hx9 := hregs.x9_eq
    by_cases hidx : idx < bs.length
    · have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = false :=
        fu_ule_false hidx hlen
      have hnext : SfuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post :=
        fun idx' sn hlt hle' hval' hpc' hregs' =>
          ih idx' sn hle' (by omega) hval' hpc' hregs'
      apply rustSepWP_cut (mid := sfuPl.base + 52#64)
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      exact fuAt34 hlen hpost hnext hidx hval rfl (fu_keep_regs hregs hrun)
    · have heof : idx = bs.length := by omega
      have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = true := by
        rw [heof]; exact fu_ule_true
      have hok : runUtf8Validation bs = .ok () := by
        rw [hval, drop_eq_nil_of_eq_len heof]; rfl
      apply rustSepWP_cut (mid := sfuPl.base + 524#64)
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      exact sfuRetOk hpost hok rfl (fu_step_pres hregs.pres hrun)
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1])
        (by simp [arm64_norm, hregs.x8_eq])

/-! ## 2. Prologue & Top-Level `coreFromUtf8_ok` / `coreFromUtf8_subroutineOk` -/

/-- Raw memory-independent single-block `coreFromUtf8Spec` (`p ↦ₛ bs`), ready for
    `subroutine_ok_lift_pureWords_process`. -/
@[expose] def rawCoreFromUtf8Spec (tbl : BitVec 64) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 16 × BitVec 32) where
  pre := fun (p, ret, bs, b18, b20) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      s0.readReg64 .x8 = ret ∧ bs.length < 2 ^ 64⌝ ∗
      ((p ↦ₛ bs) ∗ (tbl ↦ᵣ corePlacedData1)) ∗
      (memRegion ret 18 ∗ ((ret + 18#64) ↦₁₆ b18) ∗ ((ret + 20#64) ↦₃₂ b20))
  post := fun (p, ret, bs, b18, b20) _s0 _sf =>
    ((p ↦ₛ bs) ∗ (tbl ↦ᵣ corePlacedData1)) ∗
      fromUtf8SretPost ret p bs.length b18 b20 (runUtf8Validation bs)

private theorem sfuBlock1RW_raw_ok [SingleFromUtf8Pl] :
    subroutine_ok (sfuPC.rebase sfuPl.base (fun _ => none)) sfuPl.base
      (rawCoreFromUtf8Spec (sfuPl.ρ coreUtf8CharWidthSym)) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨p, ret, bs, b18, b20⟩ R s0 hpc0 hrun0 hpre _hsp0
  let tbl := sfuPl.ρ coreUtf8CharWidthSym
  have htbl_eq : sfuPl.ρ coreUtf8CharWidthSym + 0#64 = tbl := by
    change tbl + 0#64 = tbl; bv_lin
  dsimp only [rawCoreFromUtf8Spec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0_0, hx1_0, hx8_0, hlen⟩, hpre⟩
  rw [memRegion18_eq ret] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨s17, s16, s_w8, s_w0, hpre⟩
  have hpre' : s0.mem ⊨ fuWorkPre p tbl ret bs s_w0 s_w8 s16 s17 b18 b20 ∗ R :=
    Satisfies.mono (by dsimp only [fuWorkPre]; sep_entail) hpre
  refine ⟨_, hpre', ?_⟩
  suffices hgo : ∀ (post : State → SepProp → Prop), FuPostCont s0 p tbl ret bs b18 b20 post →
      SepWP (sfuPC.rebase sfuPl.base (fun _ => none)) (s0.readReg64 .lr) s0
        (fuWorkPre p tbl ret bs s_w0 s_w8 s16 s17 b18 b20) post by
    refine hgo _ fun sf Q hpres_f _hpc_f hQ => ⟨fun hm_f => ?_, hpres_f.sp_eq, hpres_f.cs⟩
    exact Satisfies.mono
      (sepConj_mono_left (Entails.trans hQ (by dsimp only [fuPostProp]; sep_entail))) hm_f
  intro post hpost
  by_cases hempty : bs.length = 0
  · have hlen0 : BitVec.ofNat 64 bs.length = 0#64 := by simp [hempty]
    have hok : runUtf8Validation bs = .ok () := by
      cases bs with
      | nil => rfl
      | cons _ _ => simp at hempty
    apply rustSepWP_cut (mid := sfuPl.base + 524#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun0) ?_
    exact sfuRetOk hpost hok rfl (fu_step_pres (FuPreserved.refl hrun0) hrun0)
      (by simp [arm64_norm, hx0_0]) (by simp [arm64_norm, hx1_0]) (by simp [arm64_norm, hx8_0])
  · have hpos : 0 < bs.length := Nat.pos_of_ne_zero hempty
    have hne0 : (BitVec.ofNat 64 bs.length == 0#64) = false := beq_false_of_ne fun heq => by
      have htn := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen] at htn; exact hempty htn
    have hnext0 : SfuNextCont s0 p tbl ret s_w0 s_w8 s16 s17 b18 b20 bs 0 post :=
      fun idx' sn _ hle' hval' hpc_n hregs_n =>
        fuMainLoop bs.length hlen hpost idx' sn hle' (by omega) hval' hpc_n hregs_n
    apply rustSepWP_cut (mid := sfuPl.base + 52#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun0) ?_
    refine fuAt34 hlen hpost hnext0 hpos rfl rfl
      ⟨fu_step_pres (FuPreserved.refl hrun0) hrun0, by simp [arm64_norm, hx0_0],
        by simp [arm64_norm, hx1_0], by simp [arm64_norm, hx8_0], by simp [arm64_norm],
        by simpa [arm64_norm] using fu_sub15_csel hlen, by simp [arm64_norm, utf8AlignOff],
        by simpa [arm64_norm] using htbl_eq⟩

/-- Single-block `pureWordsProg` correctness of `core::str::converts::from_utf8` on read-write
    slices (`p ↦ₛ bs`) under any single-block placement `hpl : fromUtf8Block.Placeable pl`. -/
theorem pureWordsProg_rawCoreFromUtf8_ok {pl : Placement}
    (hpl : fromUtf8Block.Placeable pl) :
    subroutine_ok (pureWordsProg pl.base (fromUtf8PatchedWords pl)) pl.base
      (rawCoreFromUtf8Spec (pl.ρ coreUtf8CharWidthSym)) :=
  @subroutine_ok_pureWords_of_sfuRebase ⟨pl, hpl⟩ _ _ (@sfuBlock1RW_raw_ok ⟨pl, hpl⟩)

end

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlockRW
