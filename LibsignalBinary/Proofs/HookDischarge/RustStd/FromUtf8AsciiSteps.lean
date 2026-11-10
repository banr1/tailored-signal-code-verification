/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.Wave2.FromUtf8RO
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `.rodata`-Free ASCII-Only Stepping Proofs for `core::str::converts::from_utf8` (`LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8AsciiSteps`)

Proves that on pure-ASCII byte slices (`∀ b ∈ bs, b.toNat < 128`), `coreMultiLib` block `1`
(`fuLib1` / `fuTree1`, `156` words = `624` B) never enters the multi-byte branch `+0x90` and never
reads `corePlacedData1` (`UTF8_CHAR_WIDTH`) from memory, satisfying both read-only
(`fromUtf8AsciiSpecRO hookStack`) and read-write (`fromUtf8AsciiSpec hookStack`) contracts with
**no `withRoData` premise**.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8AsciiSteps

open Arm64 ProofLib
open Arm64.Obj (MultiPlacement MultiPlacedLib)
open VerifiedLibraries.RustStd (coreMultiLib coreFromUtf8Sym coreUtf8CharWidthSym
  CoreFromUtf8Pl fuMpl fuPl1 fuPC1 sepWP_seg_block1_pure FuPreserved FuLoopRegs
  utf8AlignOff bv64_ofNat_add_small fu_ule_false fu_ule_true pointsToBytesRO_focus8
  pointsToBytes_focus16_at rustSepWP_cut)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8 (fromUtf8AsciiSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (fromUtf8AsciiSpecRO
  pointsToBytesRO_lt_addr_space_of_pointsTo64 memRegion_24_words)

theorem sliceRO_lt_two_pow_64_of_sep_region24 {m : Memory} {p r : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp}
    (h : m ⊨ (p ↦ᵣ bs) ∗ (memRegion r 24 ∗ R)) :
    bs.length < 2 ^ 64 := by
  rw [memRegion_24_words r] at h
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at h
  rcases h with ⟨w2, w1, w0, hw⟩
  have hw' :
      m ⊨ (p ↦ᵣ bs) ∗ ((r ↦₆₄ w0) ∗ (((r + 8#64) ↦₆₄ w1) ∗ (((r + 16#64) ↦₆₄ w2) ∗ R))) :=
    Satisfies.mono (by sep_entail) hw
  exact pointsToBytesRO_lt_addr_space_of_pointsTo64 hw'

private theorem sliceRW_lt_two_pow_64_of_sep_region24 {m : Memory} {p r : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp}
    (h : m ⊨ (p ↦ₛ bs) ∗ (memRegion r 24 ∗ R)) :
    bs.length < 2 ^ 64 := by
  have hle : bs.length ≤ 2 ^ 64 := ((IsBlock.pointsToBytes p bs).read h).1
  by_cases heq : bs.length = 2 ^ 64
  · exfalso
    have hd := (IsBlock.pointsToBytes p bs).disjoint (IsBlock.memRegion r 24)
      (by omega) (by decide) h
    have hd1 := hd.1
    have hlt := (r - p).isLt
    omega
  · omega

private theorem ascii_getD_lt_0x80 {bs : List (BitVec 8)} {idx : Nat}
    (hascii : ∀ b ∈ bs, b.toNat < 128) (hidx : idx < bs.length) :
    bs.getD idx 0#8 < 0x80#8 := by
  induction bs generalizing idx with
  | nil => nomatch hidx
  | cons b0 tail ih =>
    cases idx with
    | zero => exact BitVec.lt_def.mpr (hascii b0 List.mem_cons_self)
    | succ k =>
      exact ih (fun b hb => hascii b (List.mem_cons_of_mem b0 hb))
        (by simp only [List.length_cons] at hidx; omega)

private theorem pointsToBytesRO_focus16_at_local (p : BitVec 64) (bs : List (BitVec 8))
    {idx : Nat} (h16 : idx + 16 ≤ bs.length) :
    ∃ w0 w1 : BitVec 64,
      (p ↦ᵣ bs) = ((p + BitVec.ofNat 64 idx) ↦₆₄ᵣ w0) ∗
        (((p + BitVec.ofNat 64 idx) + 8#64) ↦₆₄ᵣ w1) ∗
        ((p ↦ᵣ bs.take idx) ∗ ((p + BitVec.ofNat 64 (idx + 16)) ↦ᵣ bs.drop (idx + 16))) := by
  have hlen16 : ((bs.drop idx).take 16).length = 16 := by simp; omega
  obtain ⟨w0, w1, hchunk, _⟩ := exists_unpack64_of_length_16 hlen16
  refine ⟨w0, w1, ?_⟩
  rw [pointsToBytesRO_split3 p bs idx 16 h16, hchunk, pointsToBytesRO_append,
      show (unpack64 w0).length = 8 from rfl, show BitVec.ofNat 64 8 = 8#64 from rfl,
      ← pointsTo64RO_eq_pointsToBytesRO, ← pointsTo64RO_eq_pointsToBytesRO]
  sep_ac_rfl

private theorem fu_tbnz31_64_local (b0 : BitVec 8) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b0))).getLsbD 31 =
      !(decide (b0 < 0x80#8)) := by revert b0; decide

private theorem fu_tbnz31_32_local (b0 : BitVec 8) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b0)))).getLsbD 31 =
      !(decide (b0 < 0x80#8)) := by revert b0; decide

private theorem fu_tbnz31_se_local (b0 : BitVec 8) :
    (b0.signExtend 32).getLsbD 31 = !(decide (b0 < 0x80#8)) := by revert b0; decide

private theorem fu_tbnz31_ascii_local {b0 : BitVec 8} (hb0 : b0 < 0x80#8) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b0))).getLsbD 31 = false ∧
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b0)))).getLsbD 31 = false ∧
    (b0.signExtend 32).getLsbD 31 = false := by
  refine ⟨?_, ?_, ?_⟩
  · rw [fu_tbnz31_64_local, decide_eq_true hb0]; rfl
  · rw [fu_tbnz31_32_local, decide_eq_true hb0]; rfl
  · rw [fu_tbnz31_se_local, decide_eq_true hb0]; rfl

private theorem fu_bne_len_local {k n : Nat} (hle : k ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n != BitVec.ofNat 64 k) = decide (k < n) := by
  by_cases hlt : k < n
  · have hne : BitVec.ofNat 64 n ≠ BitVec.ofNat 64 k := fun heq => by
      have htn := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
        Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)] at htn
      omega
    simp [bne_iff_ne, hne, hlt]
  · obtain rfl : k = n := by omega
    simp

private theorem fu_ule_sub15_local {idx n : Nat} (hle : idx ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - 15)).ule (BitVec.ofNat 64 idx) = decide (¬ (idx + 16 ≤ n)) := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n - 15 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show idx < 2 ^ 64 by omega)]
  by_cases h16 : idx + 16 ≤ n
  · have h1 : ¬ (n - 15 ≤ idx) := by omega
    simp [h16, h1]
  · have h1 : n - 15 ≤ idx := by omega
    simp [h16, h1]

private theorem fu_sub15_csel_local {n : Nat} (hn : n < 2 ^ 64) :
    (if (BitVec.ofNat 64 n).ult 15#64 = true then 0#64
     else BitVec.ofNat 64 n - 15#64) = BitVec.ofNat 64 (n - 15) := by
  by_cases h15 : n < 15
  · have hult : (BitVec.ofNat 64 n).ult 15#64 = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat, show (15#64).toNat = 15 from rfl]; omega
    simp [hult, show n - 15 = 0 by omega]
  · have hult : (BitVec.ofNat 64 n).ult 15#64 = false := by
      simp [BitVec.ult, BitVec.toNat_ofNat, show (15#64).toNat = 15 from rfl]; omega
    simp only [hult, Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-! ## 1. Read-Only Slice (`p ↦ᵣ bs`) Stepping -/

section
open Arm64.Process ProofLib.ProgramReflection ProofLib.GenPlacedFetches
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

private def fuWorkPreAsciiRO (p ret : BitVec 64) (bs : List (BitVec 8))
    (s0 s8 s16 : BitVec 64) : SepProp :=
  (p ↦ᵣ bs) ∗ (ret ↦₆₄ s0) ∗ ((ret + 8#64) ↦₆₄ s8) ∗ ((ret + 16#64) ↦₆₄ s16)

private def fuPostPropAsciiRO (p ret : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (p ↦ᵣ bs) ∗ (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ p) ∗
    ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)

private abbrev FuPostContAsciiRO (s_entry : State) (p ret : BitVec 64) (bs : List (BitVec 8))
    (post : State → SepProp → Prop) : Prop :=
  ∀ (sf : State) (Q : SepProp), FuPreserved s_entry sf → sf.pc = s_entry.readReg64 .lr →
    (Q ⊢ fuPostPropAsciiRO p ret bs) → post sf Q

private theorem fuRetOkAsciiRO [CoreFromUtf8Pl] {s_entry s : State}
    {p ret s0 s8 s16 : BitVec 64} {bs : List (BitVec 8)} {post : State → SepProp → Prop}
    (hpost : FuPostContAsciiRO s_entry p ret bs post)
    (hpc : s.pc = fuPl1.base + 524#64) (hpres : FuPreserved s_entry s)
    (hx0 : s.readReg64 .x0 = p) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs.length)
    (hx8 : s.readReg64 .x8 = ret) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreAsciiRO p ret bs s0 s8 s16) post := by
  have hrun := hpres.running
  have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPreAsciiRO]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun)
    (hpost _ _ (fu_step_pres hpres hrun) rfl ?_)
  dsimp only [fuPostPropAsciiRO]; sep_entail

private theorem fuLoopCAsciiRO [CoreFromUtf8Pl] (rem : Nat) {s_entry s : State}
    {p tbl ret s0 s8 s16 : BitVec 64} {bs : List (BitVec 8)} {idx : Nat}
    {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64) (hascii : ∀ b ∈ bs, b.toNat < 128)
    (hrem : bs.length - idx ≤ rem) (hpost : FuPostContAsciiRO s_entry p ret bs post)
    (hidx : idx < bs.length) (hpc : s.pc = fuPl1.base + 120#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreAsciiRO p ret bs s0 s8 s16) post := by
  induction rem generalizing idx s with
  | zero => omega
  | succ rem ih =>
    have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
    obtain ⟨htb64, htb32, htbse⟩ := fu_tbnz31_ascii_local (ascii_getD_lt_0x80 hascii hidx)
    have h9_1 : BitVec.ofNat 64 idx + 1#64 = BitVec.ofNat 64 (idx + 1) := bv64_ofNat_add_small idx 1
    by_cases h1 : idx + 1 < bs.length
    · have hne : (BitVec.ofNat 64 bs.length != BitVec.ofNat 64 (idx + 1)) = true := by
        rw [fu_bne_len_local (by omega) hlen]; simp [h1]
      apply rustSepWP_cut (mid := fuPl1.base + 120#64)
      wp_conv_pre => rw [fuWorkPreAsciiRO, pointsToBytesRO_focus8 p bs idx hidx]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← pointsToBytesRO_focus8 p bs idx hidx, ← fuWorkPreAsciiRO]
      refine ih (by omega) h1 rfl
        ⟨fu_step_pres hregs.pres hrun, by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
          by simp [arm64_norm, hregs.x8_eq], by simp only [arm64_norm],
          by simp [arm64_norm, hregs.x10_eq], by simp [arm64_norm, hregs.x11_eq],
          by simp [arm64_norm, hregs.x12_eq]⟩
    · have hne : (BitVec.ofNat 64 bs.length != BitVec.ofNat 64 (idx + 1)) = false := by
        rw [fu_bne_len_local (by omega) hlen]; simp [h1]
      apply rustSepWP_cut (mid := fuPl1.base + 524#64)
      wp_conv_pre => rw [fuWorkPreAsciiRO, pointsToBytesRO_focus8 p bs idx hidx]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← pointsToBytesRO_focus8 p bs idx hidx, ← fuWorkPreAsciiRO]
      exact fuRetOkAsciiRO hpost rfl (fu_step_pres hregs.pres hrun)
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hregs.x8_eq])

private theorem fuAt70AsciiRO [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 s16 : BitVec 64} {bs : List (BitVec 8)} {idx : Nat}
    {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64) (hascii : ∀ b ∈ bs, b.toNat < 128)
    (hpost : FuPostContAsciiRO s_entry p ret bs post) (hle : idx ≤ bs.length)
    (hpc : s.pc = fuPl1.base + 112#64) (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreAsciiRO p ret bs s0 s8 s16) post := by
  have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
  by_cases hidx : idx < bs.length
  · have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = false := fu_ule_false hidx hlen
    apply rustSepWP_cut (mid := fuPl1.base + 120#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuLoopCAsciiRO (bs.length - idx) hlen hascii (Nat.le_refl _) hpost hidx rfl
      (fu_keep_regs hregs hrun)
  · have heof : idx = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = true := by
      rw [heof]; exact fu_ule_true
    apply rustSepWP_cut (mid := fuPl1.base + 524#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetOkAsciiRO hpost rfl (fu_step_pres hregs.pres hrun)
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hregs.x8_eq])

private theorem fuLoopBAsciiRO [CoreFromUtf8Pl] (rem : Nat) {s_entry s : State}
    {p tbl ret s0 s8 s16 : BitVec 64} {bs : List (BitVec 8)} {idx : Nat}
    {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64) (hascii : ∀ b ∈ bs, b.toNat < 128)
    (hrem : bs.length - idx ≤ rem) (hpost : FuPostContAsciiRO s_entry p ret bs post)
    (hle : idx ≤ bs.length) (hpc : s.pc = fuPl1.base + 84#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreAsciiRO p ret bs s0 s8 s16) post := by
  induction rem generalizing idx s with
  | zero =>
    have hrun := hregs.pres.running; have hx9 := hregs.x9_eq; have hx10 := hregs.x10_eq
    have h16 : ¬ (idx + 16 ≤ bs.length) := by omega
    have hcs : (BitVec.ofNat 64 (bs.length - 15)).ule (BitVec.ofNat 64 idx) = true := by
      rw [fu_ule_sub15_local hle hlen]; simp [h16]
    apply rustSepWP_cut (mid := fuPl1.base + 112#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuAt70AsciiRO hlen hascii hpost hle rfl (fu_keep_regs hregs hrun)
  | succ rem ih =>
    have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq; have hx10 := hregs.x10_eq
    by_cases h16 : idx + 16 ≤ bs.length
    · have hcs : (BitVec.ofNat 64 (bs.length - 15)).ule (BitVec.ofNat 64 idx) = false := by
        rw [fu_ule_sub15_local hle hlen]; simp [h16]
      obtain ⟨w0, w1, hfocus16⟩ := pointsToBytesRO_focus16_at_local p bs h16
      cases hswar : (((w1 ||| w0) &&& 0x8080808080808080#64) == 0#64)
      · apply rustSepWP_cut (mid := fuPl1.base + 112#64)
        wp_conv_pre => rw [fuWorkPreAsciiRO, hfocus16]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← hfocus16, ← fuWorkPreAsciiRO]
        exact fuAt70AsciiRO hlen hascii hpost hle rfl (fu_keep_regs hregs hrun)
      · have h9_16 : BitVec.ofNat 64 idx + 16#64 = BitVec.ofNat 64 (idx + 16) :=
          bv64_ofNat_add_small idx 16
        apply rustSepWP_cut (mid := fuPl1.base + 84#64)
        wp_conv_pre => rw [fuWorkPreAsciiRO, hfocus16]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← hfocus16, ← fuWorkPreAsciiRO]
        refine ih (idx := idx + 16) (by omega) (by omega) rfl
          ⟨fu_step_pres hregs.pres hrun, by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
            by simp [arm64_norm, hregs.x8_eq], by simp only [arm64_norm, hx9, h9_16],
            by simp [arm64_norm, hx10], by simp [arm64_norm, hregs.x11_eq],
            by simp [arm64_norm, hregs.x12_eq]⟩
    · have hcs : (BitVec.ofNat 64 (bs.length - 15)).ule (BitVec.ofNat 64 idx) = true := by
        rw [fu_ule_sub15_local hle hlen]; simp [h16]
      apply rustSepWP_cut (mid := fuPl1.base + 112#64); wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      exact fuAt70AsciiRO hlen hascii hpost hle rfl (fu_keep_regs hregs hrun)

private theorem fuAt34AsciiRO [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 s16 : BitVec 64} {bs : List (BitVec 8)} {idx : Nat}
    {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64) (hascii : ∀ b ∈ bs, b.toNat < 128)
    (hpost : FuPostContAsciiRO s_entry p ret bs post)
    (hnext : ∀ (idx' : Nat) (sn : State), idx < idx' → idx' ≤ bs.length →
      sn.pc = fuPl1.base + 44#64 → FuLoopRegs s_entry sn p tbl ret bs.length idx' →
      SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) sn
        (fuWorkPreAsciiRO p ret bs s0 s8 s16) post)
    (hidx : idx < bs.length) (hpc : s.pc = fuPl1.base + 52#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreAsciiRO p ret bs s0 s8 s16) post := by
  have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq; have hx11 := hregs.x11_eq
  obtain ⟨htb64, htb32, htbse⟩ := fu_tbnz31_ascii_local (ascii_getD_lt_0x80 hascii hidx)
  let alignDiff : BitVec 64 :=
    BitVec.zeroExtend 64 (BitVec.truncate 32 (utf8AlignOff p) - BitVec.truncate 32 (BitVec.ofNat 64 idx))
  cases halign : ((alignDiff &&& 7#64) == 0#64)
  · have halign_f : ((BitVec.zeroExtend 64 (BitVec.truncate 32 (utf8AlignOff p) -
        BitVec.truncate 32 (BitVec.ofNat 64 idx)) &&& 7#64) == 0#64) = false := halign
    have h9_1 : BitVec.ofNat 64 idx + 1#64 = BitVec.ofNat 64 (idx + 1) := bv64_ofNat_add_small idx 1
    apply rustSepWP_cut (mid := fuPl1.base + 44#64)
    wp_conv_pre => rw [fuWorkPreAsciiRO, pointsToBytesRO_focus8 p bs idx hidx]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    wp_conv_pre => rw [← pointsToBytesRO_focus8 p bs idx hidx, ← fuWorkPreAsciiRO]
    exact hnext (idx + 1) _ (by omega) (by omega) rfl
      ⟨fu_step_pres hregs.pres hrun, by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
        by simp [arm64_norm, hregs.x8_eq], by simp only [arm64_norm, hx9, h9_1],
        by simp [arm64_norm, hregs.x10_eq], by simp [arm64_norm, hx11],
        by simp [arm64_norm, hregs.x12_eq]⟩
  · have halign_t : ((BitVec.zeroExtend 64 (BitVec.truncate 32 (utf8AlignOff p) -
        BitVec.truncate 32 (BitVec.ofNat 64 idx)) &&& 7#64) == 0#64) = true := halign
    apply rustSepWP_cut (mid := fuPl1.base + 84#64)
    wp_conv_pre => rw [fuWorkPreAsciiRO, pointsToBytesRO_focus8 p bs idx hidx]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    wp_conv_pre => rw [← pointsToBytesRO_focus8 p bs idx hidx, ← fuWorkPreAsciiRO]
    exact fuLoopBAsciiRO (bs.length - idx) hlen hascii (Nat.le_refl _) hpost (by omega) rfl
      (fu_keep_regs hregs hrun)

private theorem fuMainLoopAsciiRO [CoreFromUtf8Pl] (rem : Nat) {s_entry : State}
    {p tbl ret s0 s8 s16 : BitVec 64} {bs : List (BitVec 8)}
    (hlen : bs.length < 2 ^ 64) (hascii : ∀ b ∈ bs, b.toNat < 128)
    {post : State → SepProp → Prop} (hpost : FuPostContAsciiRO s_entry p ret bs post)
    (idx : Nat) (s : State) (hle : idx ≤ bs.length) (hrem : bs.length - idx ≤ rem)
    (hpc : s.pc = fuPl1.base + 44#64) (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreAsciiRO p ret bs s0 s8 s16) post := by
  induction rem generalizing idx s with
  | zero =>
    have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
    have heof : idx = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = true := by
      rw [heof]; exact fu_ule_true
    apply rustSepWP_cut (mid := fuPl1.base + 524#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetOkAsciiRO hpost rfl (fu_step_pres hregs.pres hrun)
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hregs.x8_eq])
  | succ rem ih =>
    have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
    by_cases hidx : idx < bs.length
    · have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = false := fu_ule_false hidx hlen
      apply rustSepWP_cut (mid := fuPl1.base + 52#64); wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      exact fuAt34AsciiRO hlen hascii hpost
        (fun idx' sn _ hle' hpc' hregs' => ih idx' sn hle' (by omega) hpc' hregs')
        hidx rfl (fu_keep_regs hregs hrun)
    · have heof : idx = bs.length := by omega
      have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = true := by
        rw [heof]; exact fu_ule_true
      apply rustSepWP_cut (mid := fuPl1.base + 524#64); wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      exact fuRetOkAsciiRO hpost rfl (fu_step_pres hregs.pres hrun)
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hregs.x8_eq])

private def rawAsciiSpecRO : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (r, p, bs) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      s0.readReg64 (.gpr 8#5) = r ∧ ∀ b ∈ bs, b.toNat < 128⌝ ∗
      (p ↦ᵣ bs) ∗ memRegion r 24
  post := fun (r, p, bs) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗ (p ↦ᵣ bs) ∗ (r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ p) ∗
      ((r + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)

private theorem rawAsciiSpecRO_simulates_keepsFs (hookStack : Nat) :
    SpecSimulates rawAsciiSpecRO (keepsFs (fromUtf8AsciiSpecRO hookStack)) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨r, p, bs⟩ R s0 hpre
  dsimp only [keepsFs, fromUtf8AsciiSpecRO] at hpre
  refine ⟨(r, p, bs), stackAt s0.sp hookStack ∗ R, ?_, ?_⟩
  · dsimp only [rawAsciiSpecRO]
    exact Satisfies.mono (by sep_entail) hpre
  · intro sf _hret _hcc hpost
    dsimp only [rawAsciiSpecRO] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨htr, hfs⟩, hpost⟩ := hpost
    dsimp only [keepsFs, fromUtf8AsciiSpecRO]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htr, hfs⟩, Satisfies.mono (by sep_entail) hpost⟩

private theorem fuBlock1AsciiRO_raw_ok [CoreFromUtf8Pl] {P : Program}
    (hext_blk : ∀ off : Nat, off < 624 → P.externAt? (fuMpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr fuMpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded fuMpl rawAsciiSpecRO) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ret, p, bs⟩ R s0 hpc0 hrun0 hpre _hsp0
  have hfn : coreMultiLib.fnAddr fuMpl coreFromUtf8Sym = fuPl1.base := by
    change fuMpl.base 1 + 0#64 = fuMpl.base 1; bv_lin
  have htbl_eq : fuPl1.ρ coreUtf8CharWidthSym + 0#64 = fuMpl.ρ coreUtf8CharWidthSym := by
    change fuMpl.ρ coreUtf8CharWidthSym + 0#64 = fuMpl.ρ coreUtf8CharWidthSym; bv_lin
  let tbl := fuMpl.ρ coreUtf8CharWidthSym
  dsimp only [MultiPlacedLib.withCodeLoaded, rawAsciiSpecRO] at hpre ⊢
  rw [sepConj_comm _ ⌜coreMultiLib.CodeLoaded fuMpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0_0, hx1_0, hx8_0, hascii⟩, hpre⟩
  rw [sepConj_assoc] at hpre
  have hlen : bs.length < 2 ^ 64 := sliceRO_lt_two_pow_64_of_sep_region24 hpre
  rw [memRegion_24_words ret] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hpre
  rcases hpre with ⟨s_w16, s_w8, s_w0, hpre⟩
  have hpre' : s0.mem ⊨ fuWorkPreAsciiRO p ret bs s_w0 s_w8 s_w16 ∗ R :=
    Satisfies.mono (by dsimp only [fuWorkPreAsciiRO]; sep_entail) hpre
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
      FuPostContAsciiRO s' p ret bs post →
      SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s'.readReg64 .lr) s'
        (fuWorkPreAsciiRO p ret bs s_w0 s_w8 s_w16) post by
    refine hgo _ fun sf' Q hpres_f hpc_f hQ sm hcpu_out _hcl_out hnsp => ?_
    refine SepWP.done (hcpu_out.pc_eq.trans hpc_f) (hcpu_out.status_eq.trans hpres_f.running)
      ⟨fun hm_f => ?_, hcpu_out.sp_eq.trans (hpres_f.sp_eq.trans hcpu_in.sp_eq),
        VerifiedLibraries.RustStd.SameCpuState.calleeSavedPreserved hcpu_in hcpu_out hpres_f.cs⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hm_f
    rw [pure_sepConj_of_true ⟨hnsp.1, hnsp.2.2.2.2.2.2⟩]
    exact Entails.trans hQ (by dsimp only [fuPostPropAsciiRO]; sep_entail)
  intro post hpost
  by_cases hempty : bs.length = 0
  · have hlen0 : BitVec.ofNat 64 bs.length = 0#64 := by simp [hempty]
    apply rustSepWP_cut (mid := fuPl1.base + 524#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun') ?_
    exact fuRetOkAsciiRO hpost rfl (fu_step_pres (FuPreserved.refl hrun') hrun')
      (by simp [arm64_norm, hx0']) (by simp [arm64_norm, hx1']) (by simp [arm64_norm, hx8'])
  · have hpos : 0 < bs.length := Nat.pos_of_ne_zero hempty
    have hne0 : (BitVec.ofNat 64 bs.length == 0#64) = false := beq_false_of_ne fun heq => by
      have htn := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen] at htn; exact hempty htn
    apply rustSepWP_cut (mid := fuPl1.base + 52#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun') ?_
    refine fuAt34AsciiRO hlen hascii hpost
      (fun idx' sn _ hle' hpc_n hregs_n =>
        fuMainLoopAsciiRO bs.length hlen hascii hpost idx' sn hle' (by omega) hpc_n hregs_n)
      hpos rfl
      ⟨fu_step_pres (FuPreserved.refl hrun') hrun', by simp [arm64_norm, hx0'],
        by simp [arm64_norm, hx1'], by simp [arm64_norm, hx8'], by simp [arm64_norm],
        by simpa [arm64_norm] using fu_sub15_csel_local hlen, by simp [arm64_norm, utf8AlignOff],
        by simpa [arm64_norm] using htbl_eq⟩

end

/-- `.rodata`-free real-code discharge (`keepsFs (fromUtf8AsciiSpecRO hookStack)`). -/
theorem coreFromUtf8RO_placed_asciiRO_noRoData_keepsFs_ok {mpl : MultiPlacement}
    (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl (keepsFs (fromUtf8AsciiSpecRO hookStack))) :=
  ((rawAsciiSpecRO_simulates_keepsFs hookStack).withCodeLoaded
    coreMultiLib mpl).subroutine_ok (@fuBlock1AsciiRO_raw_ok ⟨mpl, hpl⟩ P hext)

/-! ## 2. Read-Write Slice (`p ↦ₛ bs`) Stepping -/

section
open Arm64.Process ProofLib.ProgramReflection ProofLib.GenPlacedFetches
arm64_proof_prelude

local macro "fu_step_pres_rw " h:term:max hr:term:max : term =>
  `(FuPreserved.step $h (by simpa [arm64_norm] using $hr) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [CalleeSavedPreserved, calleeSavedVRegs, arm64_norm]))

local macro "fu_keep_regs_rw " h:term:max hr:term:max : term =>
  `(FuLoopRegs.preserve $h (by simpa [arm64_norm] using $hr) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [CalleeSavedPreserved, calleeSavedVRegs, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]))

private def fuWorkPreAsciiRW (p ret : BitVec 64) (bs : List (BitVec 8))
    (s0 s8 s16 : BitVec 64) : SepProp :=
  (p ↦ₛ bs) ∗ (ret ↦₆₄ s0) ∗ ((ret + 8#64) ↦₆₄ s8) ∗ ((ret + 16#64) ↦₆₄ s16)

private def fuPostPropAsciiRW (p ret : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (p ↦ₛ bs) ∗ (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ p) ∗
    ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)

private abbrev FuPostContAsciiRW (s_entry : State) (p ret : BitVec 64) (bs : List (BitVec 8))
    (post : State → SepProp → Prop) : Prop :=
  ∀ (sf : State) (Q : SepProp), FuPreserved s_entry sf → sf.pc = s_entry.readReg64 .lr →
    (Q ⊢ fuPostPropAsciiRW p ret bs) → post sf Q

private theorem fuRetOkAsciiRW [CoreFromUtf8Pl] {s_entry s : State}
    {p ret s0 s8 s16 : BitVec 64} {bs : List (BitVec 8)} {post : State → SepProp → Prop}
    (hpost : FuPostContAsciiRW s_entry p ret bs post)
    (hpc : s.pc = fuPl1.base + 524#64) (hpres : FuPreserved s_entry s)
    (hx0 : s.readReg64 .x0 = p) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs.length)
    (hx8 : s.readReg64 .x8 = ret) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreAsciiRW p ret bs s0 s8 s16) post := by
  have hrun := hpres.running
  have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPreAsciiRW]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun)
    (hpost _ _ (fu_step_pres_rw hpres hrun) rfl ?_)
  dsimp only [fuPostPropAsciiRW]; sep_entail

private theorem fuLoopCAsciiRW [CoreFromUtf8Pl] (rem : Nat) {s_entry s : State}
    {p tbl ret s0 s8 s16 : BitVec 64} {bs : List (BitVec 8)} {idx : Nat}
    {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64) (hascii : ∀ b ∈ bs, b.toNat < 128)
    (hrem : bs.length - idx ≤ rem) (hpost : FuPostContAsciiRW s_entry p ret bs post)
    (hidx : idx < bs.length) (hpc : s.pc = fuPl1.base + 120#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreAsciiRW p ret bs s0 s8 s16) post := by
  induction rem generalizing idx s with
  | zero => omega
  | succ rem ih =>
    have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
    obtain ⟨htb64, htb32, htbse⟩ := fu_tbnz31_ascii_local (ascii_getD_lt_0x80 hascii hidx)
    have h9_1 : BitVec.ofNat 64 idx + 1#64 = BitVec.ofNat 64 (idx + 1) := bv64_ofNat_add_small idx 1
    by_cases h1 : idx + 1 < bs.length
    · have hne : (BitVec.ofNat 64 bs.length != BitVec.ofNat 64 (idx + 1)) = true := by
        rw [fu_bne_len_local (by omega) hlen]; simp [h1]
      apply rustSepWP_cut (mid := fuPl1.base + 120#64)
      wp_conv_pre => rw [fuWorkPreAsciiRW, pointsToBytes_focus8 p bs idx hidx]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← pointsToBytes_focus8 p bs idx hidx, ← fuWorkPreAsciiRW]
      refine ih (by omega) h1 rfl
        ⟨fu_step_pres_rw hregs.pres hrun, by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
          by simp [arm64_norm, hregs.x8_eq], by simp only [arm64_norm],
          by simp [arm64_norm, hregs.x10_eq], by simp [arm64_norm, hregs.x11_eq],
          by simp [arm64_norm, hregs.x12_eq]⟩
    · have hne : (BitVec.ofNat 64 bs.length != BitVec.ofNat 64 (idx + 1)) = false := by
        rw [fu_bne_len_local (by omega) hlen]; simp [h1]
      apply rustSepWP_cut (mid := fuPl1.base + 524#64)
      wp_conv_pre => rw [fuWorkPreAsciiRW, pointsToBytes_focus8 p bs idx hidx]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← pointsToBytes_focus8 p bs idx hidx, ← fuWorkPreAsciiRW]
      exact fuRetOkAsciiRW hpost rfl (fu_step_pres_rw hregs.pres hrun)
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hregs.x8_eq])

private theorem fuAt70AsciiRW [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 s16 : BitVec 64} {bs : List (BitVec 8)} {idx : Nat}
    {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64) (hascii : ∀ b ∈ bs, b.toNat < 128)
    (hpost : FuPostContAsciiRW s_entry p ret bs post) (hle : idx ≤ bs.length)
    (hpc : s.pc = fuPl1.base + 112#64) (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreAsciiRW p ret bs s0 s8 s16) post := by
  have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
  by_cases hidx : idx < bs.length
  · have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = false := fu_ule_false hidx hlen
    apply rustSepWP_cut (mid := fuPl1.base + 120#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuLoopCAsciiRW (bs.length - idx) hlen hascii (Nat.le_refl _) hpost hidx rfl
      (fu_keep_regs_rw hregs hrun)
  · have heof : idx = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = true := by
      rw [heof]; exact fu_ule_true
    apply rustSepWP_cut (mid := fuPl1.base + 524#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetOkAsciiRW hpost rfl (fu_step_pres_rw hregs.pres hrun)
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hregs.x8_eq])

private theorem fuLoopBAsciiRW [CoreFromUtf8Pl] (rem : Nat) {s_entry s : State}
    {p tbl ret s0 s8 s16 : BitVec 64} {bs : List (BitVec 8)} {idx : Nat}
    {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64) (hascii : ∀ b ∈ bs, b.toNat < 128)
    (hrem : bs.length - idx ≤ rem) (hpost : FuPostContAsciiRW s_entry p ret bs post)
    (hle : idx ≤ bs.length) (hpc : s.pc = fuPl1.base + 84#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreAsciiRW p ret bs s0 s8 s16) post := by
  induction rem generalizing idx s with
  | zero =>
    have hrun := hregs.pres.running; have hx9 := hregs.x9_eq; have hx10 := hregs.x10_eq
    have h16 : ¬ (idx + 16 ≤ bs.length) := by omega
    have hcs : (BitVec.ofNat 64 (bs.length - 15)).ule (BitVec.ofNat 64 idx) = true := by
      rw [fu_ule_sub15_local hle hlen]; simp [h16]
    apply rustSepWP_cut (mid := fuPl1.base + 112#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuAt70AsciiRW hlen hascii hpost hle rfl (fu_keep_regs_rw hregs hrun)
  | succ rem ih =>
    have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq; have hx10 := hregs.x10_eq
    by_cases h16 : idx + 16 ≤ bs.length
    · have hcs : (BitVec.ofNat 64 (bs.length - 15)).ule (BitVec.ofNat 64 idx) = false := by
        rw [fu_ule_sub15_local hle hlen]; simp [h16]
      obtain ⟨w0, w1, _hchunk, hfocus16⟩ := pointsToBytes_focus16_at p bs h16
      cases hswar : (((w1 ||| w0) &&& 0x8080808080808080#64) == 0#64)
      · apply rustSepWP_cut (mid := fuPl1.base + 112#64)
        wp_conv_pre => rw [fuWorkPreAsciiRW, hfocus16]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← hfocus16, ← fuWorkPreAsciiRW]
        exact fuAt70AsciiRW hlen hascii hpost hle rfl (fu_keep_regs_rw hregs hrun)
      · have h9_16 : BitVec.ofNat 64 idx + 16#64 = BitVec.ofNat 64 (idx + 16) :=
          bv64_ofNat_add_small idx 16
        apply rustSepWP_cut (mid := fuPl1.base + 84#64)
        wp_conv_pre => rw [fuWorkPreAsciiRW, hfocus16]
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
        wp_conv_pre => rw [← hfocus16, ← fuWorkPreAsciiRW]
        refine ih (idx := idx + 16) (by omega) (by omega) rfl
          ⟨fu_step_pres_rw hregs.pres hrun, by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
            by simp [arm64_norm, hregs.x8_eq], by simp only [arm64_norm, hx9, h9_16],
            by simp [arm64_norm, hx10], by simp [arm64_norm, hregs.x11_eq],
            by simp [arm64_norm, hregs.x12_eq]⟩
    · have hcs : (BitVec.ofNat 64 (bs.length - 15)).ule (BitVec.ofNat 64 idx) = true := by
        rw [fu_ule_sub15_local hle hlen]; simp [h16]
      apply rustSepWP_cut (mid := fuPl1.base + 112#64); wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      exact fuAt70AsciiRW hlen hascii hpost hle rfl (fu_keep_regs_rw hregs hrun)

private theorem fuAt34AsciiRW [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 s16 : BitVec 64} {bs : List (BitVec 8)} {idx : Nat}
    {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64) (hascii : ∀ b ∈ bs, b.toNat < 128)
    (hpost : FuPostContAsciiRW s_entry p ret bs post)
    (hnext : ∀ (idx' : Nat) (sn : State), idx < idx' → idx' ≤ bs.length →
      sn.pc = fuPl1.base + 44#64 → FuLoopRegs s_entry sn p tbl ret bs.length idx' →
      SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) sn
        (fuWorkPreAsciiRW p ret bs s0 s8 s16) post)
    (hidx : idx < bs.length) (hpc : s.pc = fuPl1.base + 52#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreAsciiRW p ret bs s0 s8 s16) post := by
  have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq; have hx11 := hregs.x11_eq
  obtain ⟨htb64, htb32, htbse⟩ := fu_tbnz31_ascii_local (ascii_getD_lt_0x80 hascii hidx)
  let alignDiff : BitVec 64 :=
    BitVec.zeroExtend 64 (BitVec.truncate 32 (utf8AlignOff p) - BitVec.truncate 32 (BitVec.ofNat 64 idx))
  cases halign : ((alignDiff &&& 7#64) == 0#64)
  · have halign_f : ((BitVec.zeroExtend 64 (BitVec.truncate 32 (utf8AlignOff p) -
        BitVec.truncate 32 (BitVec.ofNat 64 idx)) &&& 7#64) == 0#64) = false := halign
    have h9_1 : BitVec.ofNat 64 idx + 1#64 = BitVec.ofNat 64 (idx + 1) := bv64_ofNat_add_small idx 1
    apply rustSepWP_cut (mid := fuPl1.base + 44#64)
    wp_conv_pre => rw [fuWorkPreAsciiRW, pointsToBytes_focus8 p bs idx hidx]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    wp_conv_pre => rw [← pointsToBytes_focus8 p bs idx hidx, ← fuWorkPreAsciiRW]
    exact hnext (idx + 1) _ (by omega) (by omega) rfl
      ⟨fu_step_pres_rw hregs.pres hrun, by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
        by simp [arm64_norm, hregs.x8_eq], by simp only [arm64_norm, hx9, h9_1],
        by simp [arm64_norm, hregs.x10_eq], by simp [arm64_norm, hx11],
        by simp [arm64_norm, hregs.x12_eq]⟩
  · have halign_t : ((BitVec.zeroExtend 64 (BitVec.truncate 32 (utf8AlignOff p) -
        BitVec.truncate 32 (BitVec.ofNat 64 idx)) &&& 7#64) == 0#64) = true := halign
    apply rustSepWP_cut (mid := fuPl1.base + 84#64)
    wp_conv_pre => rw [fuWorkPreAsciiRW, pointsToBytes_focus8 p bs idx hidx]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    wp_conv_pre => rw [← pointsToBytes_focus8 p bs idx hidx, ← fuWorkPreAsciiRW]
    exact fuLoopBAsciiRW (bs.length - idx) hlen hascii (Nat.le_refl _) hpost (by omega) rfl
      (fu_keep_regs_rw hregs hrun)

private theorem fuMainLoopAsciiRW [CoreFromUtf8Pl] (rem : Nat) {s_entry : State}
    {p tbl ret s0 s8 s16 : BitVec 64} {bs : List (BitVec 8)}
    (hlen : bs.length < 2 ^ 64) (hascii : ∀ b ∈ bs, b.toNat < 128)
    {post : State → SepProp → Prop} (hpost : FuPostContAsciiRW s_entry p ret bs post)
    (idx : Nat) (s : State) (hle : idx ≤ bs.length) (hrem : bs.length - idx ≤ rem)
    (hpc : s.pc = fuPl1.base + 44#64) (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPreAsciiRW p ret bs s0 s8 s16) post := by
  induction rem generalizing idx s with
  | zero =>
    have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
    have heof : idx = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = true := by
      rw [heof]; exact fu_ule_true
    apply rustSepWP_cut (mid := fuPl1.base + 524#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetOkAsciiRW hpost rfl (fu_step_pres_rw hregs.pres hrun)
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hregs.x8_eq])
  | succ rem ih =>
    have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
    have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
    by_cases hidx : idx < bs.length
    · have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = false := fu_ule_false hidx hlen
      apply rustSepWP_cut (mid := fuPl1.base + 52#64); wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      exact fuAt34AsciiRW hlen hascii hpost
        (fun idx' sn _ hle' hpc' hregs' => ih idx' sn hle' (by omega) hpc' hregs')
        hidx rfl (fu_keep_regs_rw hregs hrun)
    · have heof : idx = bs.length := by omega
      have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx) = true := by
        rw [heof]; exact fu_ule_true
      apply rustSepWP_cut (mid := fuPl1.base + 524#64); wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      exact fuRetOkAsciiRW hpost rfl (fu_step_pres_rw hregs.pres hrun)
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hregs.x8_eq])

private def rawAsciiSpecRW : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (r, p, bs) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      s0.readReg64 (.gpr 8#5) = r ∧ ∀ b ∈ bs, b.toNat < 128⌝ ∗
      (p ↦ₛ bs) ∗ memRegion r 24
  post := fun (r, p, bs) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗ (p ↦ₛ bs) ∗ (r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ p) ∗
      ((r + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)

private theorem rawAsciiSpecRW_simulates_keepsFs (hookStack : Nat) :
    SpecSimulates rawAsciiSpecRW (keepsFs (fromUtf8AsciiSpec hookStack)) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨r, p, bs⟩ R s0 hpre
  dsimp only [keepsFs, fromUtf8AsciiSpec] at hpre
  refine ⟨(r, p, bs), stackAt s0.sp hookStack ∗ R, ?_, ?_⟩
  · dsimp only [rawAsciiSpecRW]
    exact Satisfies.mono (by sep_entail) hpre
  · intro sf _hret _hcc hpost
    dsimp only [rawAsciiSpecRW] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨htr, hfs⟩, hpost⟩ := hpost
    dsimp only [keepsFs, fromUtf8AsciiSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htr, hfs⟩, Satisfies.mono (by sep_entail) hpost⟩

private theorem fuBlock1AsciiRW_raw_ok [CoreFromUtf8Pl] {P : Program}
    (hext_blk : ∀ off : Nat, off < 624 → P.externAt? (fuMpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr fuMpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded fuMpl rawAsciiSpecRW) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ret, p, bs⟩ R s0 hpc0 hrun0 hpre _hsp0
  have hfn : coreMultiLib.fnAddr fuMpl coreFromUtf8Sym = fuPl1.base := by
    change fuMpl.base 1 + 0#64 = fuMpl.base 1; bv_lin
  have htbl_eq : fuPl1.ρ coreUtf8CharWidthSym + 0#64 = fuMpl.ρ coreUtf8CharWidthSym := by
    change fuMpl.ρ coreUtf8CharWidthSym + 0#64 = fuMpl.ρ coreUtf8CharWidthSym; bv_lin
  let tbl := fuMpl.ρ coreUtf8CharWidthSym
  dsimp only [MultiPlacedLib.withCodeLoaded, rawAsciiSpecRW] at hpre ⊢
  rw [sepConj_comm _ ⌜coreMultiLib.CodeLoaded fuMpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0_0, hx1_0, hx8_0, hascii⟩, hpre⟩
  rw [sepConj_assoc] at hpre
  have hlen : bs.length < 2 ^ 64 := sliceRW_lt_two_pow_64_of_sep_region24 hpre
  rw [memRegion_24_words ret] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hpre
  rcases hpre with ⟨s_w16, s_w8, s_w0, hpre⟩
  have hpre' : s0.mem ⊨ fuWorkPreAsciiRW p ret bs s_w0 s_w8 s_w16 ∗ R :=
    Satisfies.mono (by dsimp only [fuWorkPreAsciiRW]; sep_entail) hpre
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
      FuPostContAsciiRW s' p ret bs post →
      SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s'.readReg64 .lr) s'
        (fuWorkPreAsciiRW p ret bs s_w0 s_w8 s_w16) post by
    refine hgo _ fun sf' Q hpres_f hpc_f hQ sm hcpu_out _hcl_out hnsp => ?_
    refine SepWP.done (hcpu_out.pc_eq.trans hpc_f) (hcpu_out.status_eq.trans hpres_f.running)
      ⟨fun hm_f => ?_, hcpu_out.sp_eq.trans (hpres_f.sp_eq.trans hcpu_in.sp_eq),
        VerifiedLibraries.RustStd.SameCpuState.calleeSavedPreserved hcpu_in hcpu_out hpres_f.cs⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hm_f
    rw [pure_sepConj_of_true ⟨hnsp.1, hnsp.2.2.2.2.2.2⟩]
    exact Entails.trans hQ (by dsimp only [fuPostPropAsciiRW]; sep_entail)
  intro post hpost
  by_cases hempty : bs.length = 0
  · have hlen0 : BitVec.ofNat 64 bs.length = 0#64 := by simp [hempty]
    apply rustSepWP_cut (mid := fuPl1.base + 524#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun') ?_
    exact fuRetOkAsciiRW hpost rfl (fu_step_pres_rw (FuPreserved.refl hrun') hrun')
      (by simp [arm64_norm, hx0']) (by simp [arm64_norm, hx1']) (by simp [arm64_norm, hx8'])
  · have hpos : 0 < bs.length := Nat.pos_of_ne_zero hempty
    have hne0 : (BitVec.ofNat 64 bs.length == 0#64) = false := beq_false_of_ne fun heq => by
      have htn := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen] at htn; exact hempty htn
    apply rustSepWP_cut (mid := fuPl1.base + 52#64); wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun') ?_
    refine fuAt34AsciiRW hlen hascii hpost
      (fun idx' sn _ hle' hpc_n hregs_n =>
        fuMainLoopAsciiRW bs.length hlen hascii hpost idx' sn hle' (by omega) hpc_n hregs_n)
      hpos rfl
      ⟨fu_step_pres_rw (FuPreserved.refl hrun') hrun', by simp [arm64_norm, hx0'],
        by simp [arm64_norm, hx1'], by simp [arm64_norm, hx8'], by simp [arm64_norm],
        by simpa [arm64_norm] using fu_sub15_csel_local hlen, by simp [arm64_norm, utf8AlignOff],
        by simpa [arm64_norm] using htbl_eq⟩

end

/-- `.rodata`-free real-code discharge for RW `keepsFs (fromUtf8AsciiSpec hookStack)`. -/
theorem coreFromUtf8_placed_asciiRW_noRoData_keepsFs_ok {mpl : MultiPlacement}
    (hookStack : Nat := extHookStack)
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl (keepsFs (fromUtf8AsciiSpec hookStack))) :=
  ((rawAsciiSpecRW_simulates_keepsFs hookStack).withCodeLoaded
    coreMultiLib mpl).subroutine_ok (@fuBlock1AsciiRW_raw_ok ⟨mpl, hpl⟩ P hext)

end LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8AsciiSteps
