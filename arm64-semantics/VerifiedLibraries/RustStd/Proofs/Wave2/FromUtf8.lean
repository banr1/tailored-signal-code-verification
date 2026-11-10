/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.Wave2.FromUtf8Step

/-!
# Placement-Generic `core::str::converts::from_utf8`

Placement-generic proof of `core::str::converts::from_utf8` (block `1` of `coreMultiLib`) against
`coreFromUtf8Spec`, using the 256-byte read-only `.rodata` width table at
`mpl.ρ coreUtf8CharWidthSym`.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches

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

private theorem FuNextCont.mono [CoreFromUtf8Pl] {s_entry : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx idx1 : Nat} {post : State → SepProp → Prop}
    (hle : idx ≤ idx1)
    (h : FuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post) :
    FuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx1 post :=
  fun idx' sn hlt => h idx' sn (by omega)

private theorem fu_tbnz31_64 (b0 : BitVec 8) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b0))).getLsbD 31 =
      !(decide (b0 < 0x80#8)) := by
  revert b0; decide

private theorem fu_tbnz31_32 (b0 : BitVec 8) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b0)))).getLsbD 31 =
      !(decide (b0 < 0x80#8)) := by
  revert b0; decide

private theorem fu_tbnz31_se (b0 : BitVec 8) :
    (b0.signExtend 32).getLsbD 31 = !(decide (b0 < 0x80#8)) := by
  revert b0; decide

private theorem fu_bne_len {k n : Nat} (hle : k ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n != BitVec.ofNat 64 k) = decide (k < n) := by
  by_cases hlt : k < n
  · have hne : BitVec.ofNat 64 n ≠ BitVec.ofNat 64 k := by
      intro heq
      have htn := congrArg BitVec.toNat heq
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
        Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)] at htn
      omega
    simp [bne_iff_ne, hne, hlt]
  · have heq : k = n := by omega
    subst heq; simp

private theorem fu_ule_sub15 {idx n : Nat} (hle : idx ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - 15)).ule (BitVec.ofNat 64 idx) = decide (¬ (idx + 16 ≤ n)) := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show n - 15 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show idx < 2 ^ 64 by omega)]
  by_cases h16 : idx + 16 ≤ n
  · have h1 : ¬ (n - 15 ≤ idx) := by omega
    simp [h16, h1]
  · have h1 : n - 15 ≤ idx := by omega
    simp [h16, h1]

private theorem fuLoopC [CoreFromUtf8Pl]
    (rem : Nat) {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hrem : bs.length - idx ≤ rem)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hpc : s.pc = fuPl1.base + 120#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
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
        apply rustSepWP_cut (mid := fuPl1.base + 120#64)
        wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs idx hidx]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← pointsToBytes_focus8 p bs idx hidx, ← fuWorkPre]
        refine ih (by omega) (hnext.mono (by omega)) h1 hval1 rfl
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
        apply rustSepWP_cut (mid := fuPl1.base + 524#64)
        wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs idx hidx]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← pointsToBytes_focus8 p bs idx hidx, ← fuWorkPre]
        exact fuRetOk hpost hok rfl (fu_step_pres hregs.pres hrun)
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
      apply rustSepWP_cut (mid := fuPl1.base + 144#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs idx hidx]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← pointsToBytes_focus8 p bs idx hidx, ← fuWorkPre]
      refine fuMultiByte hlen hpost hnext hidx hval hb0 rfl (fu_keep_regs hregs hrun) ?_
      simp only [arm64_norm]

private theorem fuAt70 [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hle : idx ≤ bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hpc : s.pc = fuPl1.base + 112#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running
  have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq
  have hx9 := hregs.x9_eq
  by_cases hidx : idx < bs.length
  · have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = false :=
      fu_ule_false hidx hlen
    apply rustSepWP_cut (mid := fuPl1.base + 120#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuLoopC (bs.length - idx) hlen (Nat.le_refl _) hpost hnext hidx hval rfl
      (fu_keep_regs hregs hrun)
  · have heof : idx = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = true := by
      rw [heof]; exact fu_ule_true
    have hok : runUtf8Validation bs = .ok () := by
      rw [hval, drop_eq_nil_of_eq_len heof]; rfl
    apply rustSepWP_cut (mid := fuPl1.base + 524#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetOk hpost hok rfl (fu_step_pres hregs.pres hrun)
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1])
      (by simp [arm64_norm, hregs.x8_eq])

private theorem fuLoopB [CoreFromUtf8Pl]
    (rem : Nat) {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hrem : bs.length - idx ≤ rem)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hle : idx ≤ bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hpc : s.pc = fuPl1.base + 84#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  induction rem generalizing idx s with
  | zero =>
    have hrun := hregs.pres.running
    have hx9 := hregs.x9_eq
    have hx10 := hregs.x10_eq
    have h16 : ¬ (idx + 16 ≤ bs.length) := by omega
    have hcs : (BitVec.ofNat 64 (bs.length - 15)).ule (BitVec.ofNat 64 idx) = true := by
      rw [fu_ule_sub15 hle hlen]; simp [h16]
    apply rustSepWP_cut (mid := fuPl1.base + 112#64)
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
      · apply rustSepWP_cut (mid := fuPl1.base + 112#64)
        wp_conv_pre => rw [fuWorkPre, hfocus16]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← hfocus16, ← fuWorkPre]
        exact fuAt70 hlen hpost hnext hle hval rfl (fu_keep_regs hregs hrun)
      · have hval16 := hval.trans (runUtf8ValidationLoop_swar16 h16 hchunk (beq_iff_eq.mp hswar))
        have h9_16 : BitVec.ofNat 64 idx + 16#64 = BitVec.ofNat 64 (idx + 16) :=
          bv64_ofNat_add_small idx 16
        apply rustSepWP_cut (mid := fuPl1.base + 84#64)
        wp_conv_pre => rw [fuWorkPre, hfocus16]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← hfocus16, ← fuWorkPre]
        refine ih (by omega) (hnext.mono (by omega)) (by omega) hval16 rfl
          ⟨fu_step_pres hregs.pres hrun,
            by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
            by simp [arm64_norm, hregs.x8_eq], ?_,
            by simp [arm64_norm, hx10], by simp [arm64_norm, hregs.x11_eq],
            by simp [arm64_norm, hregs.x12_eq]⟩
        simp only [arm64_norm, hx9, h9_16]
    · have hcs : (BitVec.ofNat 64 (bs.length - 15)).ule (BitVec.ofNat 64 idx) = true := by
        rw [fu_ule_sub15 hle hlen]; simp [h16]
      apply rustSepWP_cut (mid := fuPl1.base + 112#64)
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      exact fuAt70 hlen hpost hnext hle hval rfl (fu_keep_regs hregs hrun)

private theorem fuAt34 [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hpc : s.pc = fuPl1.base + 52#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
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
      apply rustSepWP_cut (mid := fuPl1.base + 44#64)
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
      apply rustSepWP_cut (mid := fuPl1.base + 84#64)
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
    apply rustSepWP_cut (mid := fuPl1.base + 144#64)
    wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs idx hidx]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    wp_conv_pre => rw [← pointsToBytes_focus8 p bs idx hidx, ← fuWorkPre]
    refine fuMultiByte hlen hpost hnext hidx hval hb0 rfl (fu_keep_regs hregs hrun) ?_
    simp only [arm64_norm]

private theorem fuMainLoop [CoreFromUtf8Pl]
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
    (hpc : s.pc = fuPl1.base + 44#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
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
    apply rustSepWP_cut (mid := fuPl1.base + 524#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetOk hpost hok rfl (fu_step_pres hregs.pres hrun)
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
      have hnext : FuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post :=
        fun idx' sn hlt hle' hval' hpc' hregs' =>
          ih idx' sn hle' (by omega) hval' hpc' hregs'
      apply rustSepWP_cut (mid := fuPl1.base + 52#64)
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      exact fuAt34 hlen hpost hnext hidx hval rfl (fu_keep_regs hregs hrun)
    · have heof : idx = bs.length := by omega
      have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = true := by
        rw [heof]; exact fu_ule_true
      have hok : runUtf8Validation bs = .ok () := by
        rw [hval, drop_eq_nil_of_eq_len heof]; rfl
      apply rustSepWP_cut (mid := fuPl1.base + 524#64)
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      exact fuRetOk hpost hok rfl (fu_step_pres hregs.pres hrun)
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1])
        (by simp [arm64_norm, hregs.x8_eq])

private theorem fu_sub15_csel {n : Nat} (hn : n < 2 ^ 64) :
    (if (BitVec.ofNat 64 n).ult 15#64 = true then 0#64
     else BitVec.ofNat 64 n - 15#64) = BitVec.ofNat 64 (n - 15) := by
  by_cases h15 : n < 15
  · have hult : (BitVec.ofNat 64 n).ult 15#64 = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, show (15#64).toNat = 15 from rfl, h15]
    have h0 : n - 15 = 0 := by omega
    simp [hult, h0]
  · have hult : (BitVec.ofNat 64 n).ult 15#64 = false := by
      simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, show (15#64).toNat = 15 from rfl]
      omega
    simp only [hult, Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    omega

private theorem fuBlock1_ok [CoreFromUtf8Pl] {P : Program}
    (hext_blk : ∀ off : Nat, off < 624 →
      P.externAt? (fuMpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr fuMpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded fuMpl (coreFromUtf8Spec (fuMpl.ρ coreUtf8CharWidthSym))) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨p, ret, bs, b18, b20⟩ R s0 hpc0 hrun0 hpre _hsp0
  have hfn : coreMultiLib.fnAddr fuMpl coreFromUtf8Sym = fuPl1.base := by
    change fuMpl.base 1 + 0#64 = fuMpl.base 1
    bv_lin
  have htbl_eq : fuPl1.ρ coreUtf8CharWidthSym + 0#64 = fuMpl.ρ coreUtf8CharWidthSym := by
    change fuMpl.ρ coreUtf8CharWidthSym + 0#64 = fuMpl.ρ coreUtf8CharWidthSym
    bv_lin
  let tbl := fuMpl.ρ coreUtf8CharWidthSym
  dsimp only [MultiPlacedLib.withCodeLoaded, coreFromUtf8Spec] at hpre ⊢
  rw [sepConj_comm _ ⌜coreMultiLib.CodeLoaded fuMpl s0.mem⌝,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0_0, hx1_0, hx8_0, hlen⟩, hpre⟩
  rw [memRegion18_eq ret] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨s17, s16, s_w8, s_w0, hpre⟩
  have hpre' : s0.mem ⊨ fuWorkPre p tbl ret bs s_w0 s_w8 s16 s17 b18 b20 ∗ R :=
    Satisfies.mono (by dsimp only [fuWorkPre]; sep_entail) hpre
  refine ⟨_, hpre', ?_⟩
  apply sepWP_seg_block1_pure hext_blk hcl (mid := s0.readReg64 .lr)
  intro s' hcpu_in
  have hlr' : s'.readReg64 .lr = s0.readReg64 .lr := hcpu_in.readReg64 .lr
  rw [← hlr']
  have hpc' : s'.pc = fuPl1.base := hcpu_in.pc_eq.trans (hpc0.trans hfn)
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = p := (hcpu_in.readReg64 .x0).trans hx0_0
  have hx1' : s'.readReg64 .x1 = BitVec.ofNat 64 bs.length := (hcpu_in.readReg64 .x1).trans hx1_0
  have hx8' : s'.readReg64 .x8 = ret := (hcpu_in.readReg64 .x8).trans hx8_0
  suffices hgo : ∀ (post : State → SepProp → Prop),
      FuPostCont s' p tbl ret bs b18 b20 post →
      SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s'.readReg64 .lr) s'
        (fuWorkPre p tbl ret bs s_w0 s_w8 s16 s17 b18 b20) post by
    refine hgo _ fun sf' Q hpres_f hpc_f hQ sm hcpu_out _hcl_out hnsp => ?_
    have hpc_sm : sm.pc = s'.readReg64 .lr := hcpu_out.pc_eq.trans hpc_f
    have hrun_sm : sm.status = .Running := hcpu_out.status_eq.trans hpres_f.running
    have hsp_sm : sm.sp = s0.sp := hcpu_out.sp_eq.trans (hpres_f.sp_eq.trans hcpu_in.sp_eq)
    have hcs_sm : CalleeSavedPreserved s0 sm :=
      SameCpuState.calleeSavedPreserved hcpu_in hcpu_out hpres_f.cs
    refine SepWP.done hpc_sm hrun_sm ⟨fun hm_f => ?_, hsp_sm, hcs_sm⟩
    refine Satisfies.mono ?_ hm_f
    apply sepConj_mono_left
    rw [pure_sepConj_of_true ⟨hnsp.1, hnsp.2.2.2.2.2.2⟩]
    exact Entails.trans hQ (by dsimp only [fuPostProp]; sep_entail)
  intro post hpost
  by_cases hempty : bs.length = 0
  · have hlen0 : BitVec.ofNat 64 bs.length = 0#64 := by simp [hempty]
    have hok : runUtf8Validation bs = .ok () := by
      cases bs with
      | nil => rfl
      | cons _ _ => simp at hempty
    apply rustSepWP_cut (mid := fuPl1.base + 524#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun') ?_
    exact fuRetOk hpost hok rfl (fu_step_pres (FuPreserved.refl hrun') hrun')
      (by simp [arm64_norm, hx0']) (by simp [arm64_norm, hx1']) (by simp [arm64_norm, hx8'])
  · have hpos : 0 < bs.length := Nat.pos_of_ne_zero hempty
    have hne0 : (BitVec.ofNat 64 bs.length == 0#64) = false := by
      apply beq_false_of_ne
      intro heq
      have htn := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen] at htn
      exact hempty htn
    have hnext0 : FuNextCont s' p tbl ret s_w0 s_w8 s16 s17 b18 b20 bs 0 post :=
      fun idx' sn _ hle' hval' hpc_n hregs_n =>
        fuMainLoop bs.length hlen hpost idx' sn hle' (by omega) hval' hpc_n hregs_n
    apply rustSepWP_cut (mid := fuPl1.base + 52#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun') ?_
    refine fuAt34 hlen hpost hnext0 hpos rfl rfl
      ⟨fu_step_pres (FuPreserved.refl hrun') hrun',
        by simp [arm64_norm, hx0'],
        by simp [arm64_norm, hx1'],
        by simp [arm64_norm, hx8'],
        by simp [arm64_norm],
        ?_,
        ?_,
        ?_⟩
    · simpa [arm64_norm] using fu_sub15_csel hlen
    · simp [arm64_norm, utf8AlignOff]
    · simpa [arm64_norm] using htbl_eq

/-- Placement-generic correctness of `core::str::converts::from_utf8` against `coreFromUtf8Spec`
    for any `P : Program` with no hooks inside `coreMultiLib` block `1`. -/
theorem coreFromUtf8_ok {mpl : MultiPlacement}
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 →
      P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl (coreFromUtf8Spec (mpl.ρ coreUtf8CharWidthSym))) := by
  letI : CoreFromUtf8Pl := ⟨mpl, hpl⟩
  exact fuBlock1_ok hext

/-- Canonical `MultiPlacedLib.subroutineOk` for `coreFromUtf8Sym` under any `externs` map. -/
theorem coreFromUtf8_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun mpl => coreFromUtf8Spec (mpl.ρ coreUtf8CharWidthSym)) externs := by
  refine ⟨by decide, 1, 0, by decide, fun mpl hpl => ?_⟩
  refine coreFromUtf8_ok hpl (fun off hoff => ?_)
  have hP1 : (coreMultiLib.blockLib 1).text.Placeable (coreMultiLib.blockPlacement mpl 1) :=
    hpl.blocks_ok 1 (by decide)
  have hlen : 0 + 624 ≤ (coreMultiLib.blockLib 1).text.code.length := by
    change 0 + 624 ≤ fuLib1.text.code.length
    rw [length_text_of_tree fu1_code_eq fu1_tree_size]; omega
  have hhf := PlacedLib.hookFree_program_noOverrides
    (lib := coreMultiLib.blockLib 1) (pl := coreMultiLib.blockPlacement mpl 1)
    (X := externs) (svc := Syscall.standard) hP1 hlen
  have hoff_eq :
      (mpl.base 1 + BitVec.ofNat 64 off -
        (coreMultiLib.blockProgram mpl 1 externs).base).toNat = off := by
    change (mpl.base 1 + BitVec.ofNat 64 off - mpl.base 1).toNat = off
    rw [Program.add_ofNat_sub_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Program.externAt?
  rw [hoff_eq]
  exact Program.hookAtOff?_eq_none_of_hookFree hhf (Nat.zero_le _) hoff

end

end VerifiedLibraries.RustStd
