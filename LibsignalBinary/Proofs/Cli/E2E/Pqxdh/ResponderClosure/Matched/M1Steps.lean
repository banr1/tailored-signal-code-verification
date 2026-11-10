/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Fetch
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import ProofLib.SepLogic.WP
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Prologue and Epilogue Symbolic Steps for `promote_matching_session`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

private theorem cond_eq_adds_1_false {c : BitVec 64} (hc : c.toNat < 2 ^ 63) :
    ConditionHolds CondCode.EQ (addsPState64 c 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat
  omega

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_sub_1184_align (sp : BitVec 64) :
    ((sp - 1184#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_sub_96_align (sp : BitVec 64) :
    ((sp - 96#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_add_1088_align (sp : BitVec 64) :
    ((sp + 1088#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_subs32_self (v : BitVec 32) :
    ConditionHolds CondCode.EQ (subsPState32 v v) = true := by
  rw [conditionHolds_eq_subsPState32, beq_self_eq_true]

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ne_subs32_self (v : BitVec 32) :
    ConditionHolds CondCode.NE (subsPState32 v v) = false := by
  rw [conditionHolds_ne_subsPState32, bne_self_eq_false]

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ne_subs64_self (v : BitVec 64) :
    ConditionHolds CondCode.NE (subsPState64 v v) = false := by
  rw [conditionHolds_ne_subsPState64, bne_self_eq_false]

@[local simp, local wp_norm, local arm64_norm]
private theorem zext64_setWidth32_byte (v : BitVec 8) :
    (v.zeroExtend 64 : BitVec 64).setWidth 32 = v.zeroExtend 32 := by
  bv_omega

@[local simp, local wp_norm, local arm64_norm]
private theorem zext64_extractLsb32_byte (v : BitVec 8) :
    (v.zeroExtend 64 : BitVec 64).extractLsb' 0 32 = v.zeroExtend 32 := by
  bv_slice

@[local simp, local wp_norm, local arm64_norm]
private theorem csel_ver_setWidth32 (sessVer : BitVec 32) :
    BitVec.setWidth 32 (if ConditionHolds CondCode.EQ (subsPState32 sessVer 0#32)
      then 2#64 else BitVec.setWidth 64 sessVer) =
    if sessVer = 0#32 then 2#32 else sessVer := by
  rw [conditionHolds_eq_subsPState32]
  by_cases h : sessVer = 0#32 <;> simp [h]

@[local simp, local wp_norm, local arm64_norm]
private theorem csel_ver_extractLsb32 (sessVer : BitVec 32) :
    BitVec.extractLsb' 0 32 (if ConditionHolds CondCode.EQ (subsPState32 sessVer 0#32)
      then 2#64 else BitVec.setWidth 64 sessVer) =
    if sessVer = 0#32 then 2#32 else sessVer := by
  rw [conditionHolds_eq_subsPState32]
  by_cases h : sessVer = 0#32
  · subst h; decide
  · simp only [beq_iff_eq, h, ↓reduceIte]
    bv_slice

def promoteSavedRegs (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

private theorem cells_96_12_eq (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      (∃∗ v0, (sp - 96#64) ↦₆₄ v0 ∗
      ∃∗ v1, (sp - 88#64) ↦₆₄ v1 ∗
      ∃∗ v2, (sp - 80#64) ↦₆₄ v2 ∗
      ∃∗ v3, (sp - 72#64) ↦₆₄ v3 ∗
      ∃∗ v4, (sp - 64#64) ↦₆₄ v4 ∗
      ∃∗ v5, (sp - 56#64) ↦₆₄ v5 ∗
      ∃∗ v6, (sp - 48#64) ↦₆₄ v6 ∗
      ∃∗ v7, (sp - 40#64) ↦₆₄ v7 ∗
      ∃∗ v8, (sp - 32#64) ↦₆₄ v8 ∗
      ∃∗ v9, (sp - 24#64) ↦₆₄ v9 ∗
      ∃∗ v10, (sp - 16#64) ↦₆₄ v10 ∗
      ∃∗ v11, (sp - 8#64) ↦₆₄ v11 ∗ emp) := by
  have hstep (k1 k2 : BitVec 64) (h : k1 - 8#64 = k2) : (sp - k1) + 8#64 = sp - k2 := by
    subst h; bv_omega
  dsimp only [cells]
  rw [hstep 96#64 88#64 rfl, hstep 88#64 80#64 rfl, hstep 80#64 72#64 rfl,
      hstep 72#64 64#64 rfl, hstep 64#64 56#64 rfl, hstep 56#64 48#64 rfl,
      hstep 48#64 40#64 rfl, hstep 40#64 32#64 rfl, hstep 32#64 24#64 rfl,
      hstep 24#64 16#64 rfl, hstep 16#64 8#64 rfl]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
theorem promote_prologue_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s0 : State) (recPtr locCap alicePtr serPtr outPtr : BitVec 64)
    (sessVer : BitVec 32) (msgVer : BitVec 8)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
    (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = recPtr)
    (hx1 : s0.readReg64 .x1 = msgVer.zeroExtend 64)
    (hx2 : s0.readReg64 .x2 = serPtr)
    (hx3 : s0.readReg64 .x3 = 33#64)
    (hx8 : s0.readReg64 .x8 = outPtr)
    (hcap : locCap.toNat < 2 ^ 63)
    (hver : (if sessVer = 0#32 then 2#32 else sessVer) = msgVer.zeroExtend 32) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64) s0
      (((recPtr + 0x18#64) ↦₆₄ locCap) ∗
       ((recPtr + 0x80#64) ↦₆₄ alicePtr) ∗
       ((recPtr + 0x88#64) ↦₆₄ 33#64) ∗
       ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗
       (∃∗ w4a0 : BitVec 64, (s0.sp - 1184#64) ↦₆₄ w4a0) ∗
       (∃∗ w470 : BitVec 64, (s0.sp - 1136#64) ↦₆₄ w470) ∗
       cells (s0.sp - 96#64) 12)
      (fun s1 P1 =>
        (P1 ⊢
          ((recPtr + 0x18#64) ↦₆₄ locCap) ∗
          ((recPtr + 0x80#64) ↦₆₄ alicePtr) ∗
          ((recPtr + 0x88#64) ↦₆₄ 33#64) ∗
          ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗
          ((s0.sp - 1184#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 1136#64) ↦₆₄ serPtr) ∗
          promoteSavedRegs s0) ∧
        s1.trace = s0.trace ∧
        s1.sp = s0.sp - 1184#64 ∧
        s1.readReg64 .x19 = alicePtr ∧
        s1.readReg64 .x21 = 33#64 ∧
        s1.readReg64 .x22 = serPtr ∧
        s1.readReg64 .x23 = outPtr ∧
        s1.readReg64 .x25 = 1#64 ∧
        s1.vregs = s0.vregs) := by
  rw [cells_96_12_eq s0.sp]
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode promoteBinCli b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0 128
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    promoteMatchingSessionName = entry
  examples_hide_fetches
  have hcmn := cond_eq_adds_1_false hcap
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = recPtr := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = msgVer.zeroExtend 64 := hx1
  have hx2' : s0.readReg64 (Reg.gpr 2#5) = serPtr := hx2
  have hx3' : s0.readReg64 (Reg.gpr 3#5) = 33#64 := hx3
  have hx8' : s0.readReg64 (Reg.gpr 8#5) = outPtr := hx8
  have hveq : ConditionHolds CondCode.NE
      (subsPState32 (if sessVer = 0#32 then 2#32 else sessVer) (msgVer.zeroExtend 32)) = false := by
    rw [hver, cond_ne_subs32_self]
  have hveq' : ConditionHolds CondCode.NE
      (subsPState32 (msgVer.zeroExtend 32) (if sessVer = 0#32 then 2#32 else sessVer)) = false := by
    rw [hver, cond_ne_subs32_self]
  wp_pull_exists
  wp_steps
  refine SepWP.done (by simp only [hpc, hcmn, hveq, hveq', wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    ⟨?_, by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [hx0', wp_norm, arm64_norm], by simp only [hx3', wp_norm, arm64_norm],
     by simp only [hx2', wp_norm, arm64_norm], by simp only [hx8', wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], rfl⟩
  unfold promoteSavedRegs
  sep_frame

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
theorem promote_epilogue_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s0 s2 : State) (outPtr : BitVec 64)
    (hpc : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xb4#64)
    (hrun : s2.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : s2.trace = s0.trace)
    (hsp : s2.sp = s0.sp - 1184#64)
    (hx0 : s2.readReg64 .x0 = 1#64)
    (hx23 : s2.readReg64 .x23 = outPtr)
    (hvregs : s2.vregs = s0.vregs) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s2
      ((∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
       (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
       promoteSavedRegs s0)
      (fun sf Pf =>
        (Pf ⊢
          (outPtr ↦₆₄ 0#64) ∗
          ((outPtr + 8#64) ↦₈ 1#8) ∗
          cells (s0.sp - 96#64) 12) ∧
        sf.trace = s0.trace ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf) := by
  unfold promoteSavedRegs
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode promoteBinCli b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0xb4 28
  code_fetches_range CryptoVerification.libsignalSessionCode promoteBinCli b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0x2e4 32
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    promoteMatchingSessionName = entry
  examples_hide_fetches
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0
  have hx23' : s2.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  wp_pull_exists
  wp_steps
  refine SepWP.done (by simp only [hpc, hsp, wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    ⟨?_, by simp only [htr, wp_norm, arm64_norm],
     by simp only [hsp, wp_norm, arm64_norm],
     ⟨by simp only [hsp, wp_norm, arm64_norm], by simp only [hsp, wp_norm, arm64_norm],
      by simp only [hsp, wp_norm, arm64_norm], by simp only [hsp, wp_norm, arm64_norm],
      by simp only [hsp, wp_norm, arm64_norm], by simp only [hsp, wp_norm, arm64_norm],
      by simp only [hsp, wp_norm, arm64_norm], by simp only [hsp, wp_norm, arm64_norm],
      by simp only [hsp, wp_norm, arm64_norm], by simp only [hsp, wp_norm, arm64_norm],
      by simp only [hsp, wp_norm, arm64_norm],
      by simp only [CalleeSavedVRegsPreserved, calleeSavedVRegs, hvregs, wp_norm, arm64_norm]⟩⟩
  rw [cells_96_12_eq s0.sp]
  sep_frame

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
