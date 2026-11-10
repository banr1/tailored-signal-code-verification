/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Raw
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Steps
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `SessionRecord::promote_matching_session` on a Matched Current Session

Relocatable `[LibsignalPlacement]` proof of `<SessionRecord>::promote_matching_session` (Block `50`)
on a matched `current_session` (`promote_matching_session_raw_placed_ok`,
`promote_matching_session_match_placed_ok`, and `promote_matching_session_match_placed_ok_at`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSession

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

private theorem cond_eq_adds_1_false_pl {c : BitVec 64} (hc : c.toNat < 2 ^ 63) :
    ConditionHolds CondCode.EQ (addsPState64 c 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat
  omega

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_sub_1184_align_pl (sp : BitVec 64) :
    ((sp - 1184#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_sub_96_align_pl (sp : BitVec 64) :
    ((sp - 96#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_add_1088_align_pl (sp : BitVec 64) :
    ((sp + 1088#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_subs32_self_pl (v : BitVec 32) :
    ConditionHolds CondCode.EQ (subsPState32 v v) = true := by
  rw [conditionHolds_eq_subsPState32, beq_self_eq_true]

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ne_subs32_self_pl (v : BitVec 32) :
    ConditionHolds CondCode.NE (subsPState32 v v) = false := by
  rw [conditionHolds_ne_subsPState32, bne_self_eq_false]

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ne_subs64_self_pl (v : BitVec 64) :
    ConditionHolds CondCode.NE (subsPState64 v v) = false := by
  rw [conditionHolds_ne_subsPState64, bne_self_eq_false]

@[local simp, local wp_norm, local arm64_norm]
private theorem zext64_setWidth32_byte_pl (v : BitVec 8) :
    (v.zeroExtend 64 : BitVec 64).setWidth 32 = v.zeroExtend 32 := by
  bv_omega

@[local simp, local wp_norm, local arm64_norm]
private theorem zext64_extractLsb32_byte_pl (v : BitVec 8) :
    (v.zeroExtend 64 : BitVec 64).extractLsb' 0 32 = v.zeroExtend 32 := by
  bv_slice

@[local simp, local wp_norm, local arm64_norm]
private theorem csel_ver_setWidth32_pl (sessVer : BitVec 32) :
    BitVec.setWidth 32 (if ConditionHolds CondCode.EQ (subsPState32 sessVer 0#32)
      then 2#64 else BitVec.setWidth 64 sessVer) =
    if sessVer = 0#32 then 2#32 else sessVer := by
  rw [conditionHolds_eq_subsPState32]
  by_cases h : sessVer = 0#32 <;> simp [h]

@[local simp, local wp_norm, local arm64_norm]
private theorem csel_ver_extractLsb32_pl (sessVer : BitVec 32) :
    BitVec.extractLsb' 0 32 (if ConditionHolds CondCode.EQ (subsPState32 sessVer 0#32)
      then 2#64 else BitVec.setWidth 64 sessVer) =
    if sessVer = 0#32 then 2#32 else sessVer := by
  rw [conditionHolds_eq_subsPState32]
  by_cases h : sessVer = 0#32
  · subst h; decide
  · simp only [beq_iff_eq, h, ↓reduceIte]
    bv_slice

private theorem cells_96_12_eq_pl (sp : BitVec 64) :
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
theorem promote_prologue_placed_wp [LibsignalPlacement]
    {H : LibsignalHooks}
    (s0 : State) (recPtr locCap alicePtr serPtr outPtr : BitVec 64)
    (sessVer : BitVec 32) (msgVer : BitVec 8)
    (hpc : s0.pc = (blkPl_50).base)
    (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = recPtr)
    (hx1 : s0.readReg64 .x1 = msgVer.zeroExtend 64)
    (hx2 : s0.readReg64 .x2 = serPtr)
    (hx3 : s0.readReg64 .x3 = 33#64)
    (hx8 : s0.readReg64 .x8 = outPtr)
    (hcap : locCap.toNat < 2 ^ 63)
    (hver : (if sessVer = 0#32 then 2#32 else sessVer) = msgVer.zeroExtend 32) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H)
      ((blkPl_50).base + 0x80#64) s0
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
  rw [cells_96_12_eq_pl s0.sp]
  have hcmn := cond_eq_adds_1_false_pl hcap
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = recPtr := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = msgVer.zeroExtend 64 := hx1
  have hx2' : s0.readReg64 (Reg.gpr 2#5) = serPtr := hx2
  have hx3' : s0.readReg64 (Reg.gpr 3#5) = 33#64 := hx3
  have hx8' : s0.readReg64 (Reg.gpr 8#5) = outPtr := hx8
  have hveq : ConditionHolds CondCode.NE
      (subsPState32 (if sessVer = 0#32 then 2#32 else sessVer) (msgVer.zeroExtend 32)) = false := by
    rw [hver, cond_ne_subs32_self_pl]
  have hveq' : ConditionHolds CondCode.NE
      (subsPState32 (msgVer.zeroExtend 32) (if sessVer = 0#32 then 2#32 else sessVer)) = false := by
    rw [hver, cond_ne_subs32_self_pl]
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
theorem promote_epilogue_placed_wp [LibsignalPlacement]
    {H : LibsignalHooks}
    (s0 s2 : State) (outPtr : BitVec 64)
    (hpc : s2.pc = (blkPl_50).base + 0xb4#64)
    (hrun : s2.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : s2.trace = s0.trace)
    (hsp : s2.sp = s0.sp - 1184#64)
    (hx0 : s2.readReg64 .x0 = 1#64)
    (hx23 : s2.readReg64 .x23 = outPtr)
    (hvregs : s2.vregs = s0.vregs) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H) (s0.readReg64 .x30) s2
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
  rw [cells_96_12_eq_pl s0.sp]
  sep_frame

/-- Mangled symbol name for `subtle::black_box::<u8>` in Block 50. -/
abbrev lsBlackBoxU8Sym : String :=
  "_RINvCsdqpLrhraQXi_6subtle9black_boxhECs2wR8L9wiBdT_16curve25519_dalek"

open Arm64.Obj ProofLib.GenPlacedFetches in
private theorem externAt?_black_box_promote_placed [LibsignalPlacement]
    {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    ((blkPC_50).rebase (blkPl_50).base H).externAt?
      (lsρ lsBlackBoxU8Sym) =
      some blackBoxHook :=
  (ls_externAt?_of_mem (prog := (blkPC_50).rebase (blkPl_50).base H) (sym := lsBlackBoxU8Sym)).trans h_bb

private theorem cond_ne_subs64_one_pl {n : Nat} (hgt : 1 < n) (hlt : n < 2 ^ 64) :
    ConditionHolds CondCode.NE (subsPState64 (BitVec.ofNat 64 n) 1#64) = true := by
  rw [conditionHolds_ne_subsPState64, bne_iff_ne]
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at hnat
  omega

@[local simp, local wp_norm, local arm64_norm]
private theorem byte_bne_zext32_self_pl (a : BitVec 8) :
    (BitVec.setWidth 32 a != BitVec.setWidth 32 a) = false :=
  bne_self_eq_false _

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_ite_1_0_pl (c : Bool) :
    BitVec.setWidth 32 (if c = true then 1#64 else 0#64) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_ite_1_0_pl (c : Bool) :
    BitVec.setWidth 8 (if c = true then 1#64 else 0#64) = if c = true then 1#8 else 0#8 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth64_ite_1_0_32_pl (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#32 else 0#32) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth64_ite_1_0_8_pl (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#8 else 0#8) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and64_ite_1_0_pl (c1 c2 : Bool) :
    ((if c1 = true then 1#64 else 0#64) &&& (if c2 = true then 1#64 else 0#64)) =
      if (c1 && c2) = true then 1#64 else 0#64 := by
  cases c1 <;> cases c2 <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and64_1_ite_1_0_pl (c : Bool) :
    ((if c = true then 1#64 else 0#64) &&& 1#64) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and64_mask32_ite_1_0_pl (c : Bool) :
    ((if c = true then 1#64 else 0#64) &&& 4294967297#64) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and32_ite_1_0_pl (c1 c2 : Bool) :
    ((if c1 = true then 1#32 else 0#32) &&& (if c2 = true then 1#32 else 0#32)) =
      if (c1 && c2) = true then 1#32 else 0#32 := by
  cases c1 <;> cases c2 <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and32_1_ite_1_0_pl (c : Bool) :
    ((if c = true then 1#32 else 0#32) &&& 1#32) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl

private theorem reaches_pc_extern_m1_pl {prog : Program} {target_pc : BitVec 64} {s : State}
    {f : State → State} {post : State → Prop} {oom : State → Prop}
    (h_run : s.status = .Running)
    (h_ext : prog.externAt? s.pc = some f)
    (h_keep : s.mem.KeepsFrozen (f s).mem)
    (h_next : reaches_pc prog target_pc (f s) post oom)
    (h_symtab : (f s).symtab = s.symtab := by rfl) :
    reaches_pc prog target_pc s post oom := by
  intro hL
  have hs := Step.extern h_run h_ext h_keep h_symtab
  rcases h_next (hs.codeLoaded hL) with ⟨sf, hsteps, hout⟩
  exact ⟨sf, Steps.step hs hsteps, hout⟩

private theorem step_blackBox_m1_pl {prog : Program} {target_pc entry_bb : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop}
    (hext : prog.externAt? entry_bb = some blackBoxHook)
    (hpc : s.pc = entry_bb)
    (hrun : s.status = .Running)
    (hs' : (s.writeReg64 .x0 (((s.readReg64 .x0).setWidth 8).zeroExtend 64)).setPC (s.readReg64 .lr) = s')
    (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at hnext ⊢
  intro R hm
  refine reaches_pc_extern_m1_pl hrun (hpc ▸ hext) (Memory.KeepsFrozen.refl _) ?_ rfl
  change reaches_pc prog target_pc
    ((s.writeReg64 .x0 (((s.readReg64 .x0).setWidth 8).zeroExtend 64)).setPC (s.readReg64 .lr)) _ _
  rw [hs']
  have hmem : s'.mem = s.mem := by rw [← hs']; rfl
  exact hnext R (hmem ▸ hm)

local macro "wp_black_box_pl" hext:ident : tactic =>
  `(tactic| (
    apply step_blackBox_m1_pl $hext
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
  ))

private theorem ofNat64_succ_sub_one_pl (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  bv_omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
private theorem promote_ct_eq_loop_last_placed_wp [LibsignalPlacement]
    {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (b0 : BitVec 8) (serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (blkPl_50).base + 0x80#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = 1#64)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H)
      ((blkPl_50).base + 0xb4#64) s
      ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))
      (fun sf Pf =>
        Pf = ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)) ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = 1#64 ∧
        sf.readReg64 .x23 = outPtr ∧
        sf.vregs = s.vregs) := by
  have hext := externAt?_black_box_promote_placed h_bb
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 1#64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 1#64 := hx25
  wp_steps
  wp_black_box_pl hext
  wp_steps
  wp_black_box_pl hext
  refine SepWP.done (by simp only [hpc, hx21', wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    ⟨rfl, by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [hx25', wp_norm, arm64_norm], by simp only [hx23', wp_norm, arm64_norm],
     rfl⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
private theorem promote_ct_eq_loop_step_placed_wp [LibsignalPlacement]
    {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (b0 : BitVec 8) (m : Nat) (hm_pos : 0 < m) (hm_lt : m + 1 < 2 ^ 64)
    (serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (blkPl_50).base + 0x80#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (m + 1))
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H)
      ((blkPl_50).base + 0x80#64) s
      ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))
      (fun s1 Pf =>
        Pf = ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)) ∧
        s1.trace = s.trace ∧
        s1.sp = s.sp ∧
        s1.readReg64 .x19 = alicePtr + 1#64 ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 m ∧
        s1.readReg64 .x22 = serPtr + 1#64 ∧
        s1.readReg64 .x23 = outPtr ∧
        s1.readReg64 .x25 = 1#64 ∧
        s1.vregs = s.vregs) := by
  have hgt : 1 < m + 1 := by omega
  have hbr := cond_ne_subs64_one_pl hgt hm_lt
  have hsub1 : BitVec.ofNat 64 (m + 1) - 1#64 = BitVec.ofNat 64 m := ofNat64_succ_sub_one_pl m
  have hext := externAt?_black_box_promote_placed h_bb
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (m + 1) := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 1#64 := hx25
  wp_steps
  wp_black_box_pl hext
  wp_steps
  refine SepWP.done (by simp only [hpc, hx21', hbr, wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    ⟨rfl, by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [hx19', wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm, hx21', hsub1],
     by simp only [hx22', wp_norm, arm64_norm],
     by simp only [hx23', wp_norm, arm64_norm],
     by simp only [hx25', wp_norm, arm64_norm],
     rfl⟩

private theorem promote_ct_eq_loop_prog_wp_pl
    (prog : Program) (loopPc exitPc outPtr : BitVec 64)
    (hlast : ∀ (b0 : BitVec 8) (serPtr alicePtr : BitVec 64) (s : State),
      s.pc = loopPc → s.status = .Running →
      s.readReg64 .x19 = alicePtr → s.readReg64 .x21 = 1#64 →
      s.readReg64 .x22 = serPtr → s.readReg64 .x23 = outPtr → s.readReg64 .x25 = 1#64 →
      SepWP prog exitPc s ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))
        (fun sf Pf =>
          Pf = ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)) ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧
          sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x23 = outPtr ∧ sf.vregs = s.vregs))
    (hstep : ∀ (b0 : BitVec 8) (m : Nat), 0 < m → m + 1 < 2 ^ 64 →
      ∀ (serPtr alicePtr : BitVec 64) (s : State),
      s.pc = loopPc → s.status = .Running →
      s.readReg64 .x19 = alicePtr → s.readReg64 .x21 = BitVec.ofNat 64 (m + 1) →
      s.readReg64 .x22 = serPtr → s.readReg64 .x23 = outPtr → s.readReg64 .x25 = 1#64 →
      SepWP prog loopPc s ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))
        (fun s1 Pf =>
          Pf = ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)) ∧
          s1.trace = s.trace ∧ s1.sp = s.sp ∧
          s1.readReg64 .x19 = alicePtr + 1#64 ∧
          s1.readReg64 .x21 = BitVec.ofNat 64 m ∧
          s1.readReg64 .x22 = serPtr + 1#64 ∧
          s1.readReg64 .x23 = outPtr ∧ s1.readReg64 .x25 = 1#64 ∧ s1.vregs = s.vregs))
    (bs : List (BitVec 8)) (hne : bs ≠ []) (hlt : bs.length < 2 ^ 64)
    (serPtr alicePtr : BitVec 64) (s : State)
    (hpc : s.pc = loopPc) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs.length)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP prog exitPc s ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs))
      (fun sf Pf =>
        Pf = ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs)) ∧
        sf.trace = s.trace ∧ sf.sp = s.sp ∧
        sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x23 = outPtr ∧ sf.vregs = s.vregs) := by
  induction bs generalizing serPtr alicePtr s with
  | nil => exact absurd rfl hne
  | cons b0 rest ih =>
    cases rest with
    | nil =>
      dsimp only [List.length_cons, List.length_nil] at hx21
      have hpre_eq : ((serPtr ↦ₛ [b0]) ∗ (alicePtr ↦ₛ [b0])) =
          ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0)) := by
        rw [pointsToBytes_cons, pointsToBytes_nil, pointsToBytes_cons, pointsToBytes_nil,
          sepConj_emp, sepConj_emp]
      rw [hpre_eq]
      exact hlast b0 serPtr alicePtr s hpc hrun hx19 hx21 hx22 hx23 hx25
    | cons b1 rest' =>
      have hm_pos : 0 < (b1 :: rest').length := by simp
      have hm_lt : (b1 :: rest').length + 1 < 2 ^ 64 := hlt
      have hlt' : (b1 :: rest').length < 2 ^ 64 := by omega
      conv =>
        arg 4
        rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
        simp only [sepConj_assoc]
      refine SepWP.bind_seq_readOnly
        (hstep b0 (b1 :: rest').length hm_pos hm_lt serPtr alicePtr s
          hpc hrun hx19 hx21 hx22 hx23 hx25)
        (by sep_focus)
        fun s1 hpc1 hrun1 ⟨htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hvregs1⟩ => ?_
      refine SepWP.bind_seq_readOnly
        (ih (by simp) hlt' (serPtr + 1#64) (alicePtr + 1#64) s1
          hpc1 hrun1 hx19_1 hx21_1 hx22_1 hx23_1 hx25_1)
        (by sep_focus)
        fun sf hpcf hrunf ⟨htrf, hspf, hx0_f, hx23_f, hvregs_f⟩ => ?_
      refine SepWP.done hpcf hrunf
        ⟨?_, htrf.trans htr1, hspf.trans hsp1, hx0_f, hx23_f, hvregs_f.trans hvregs1⟩
      rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
      ac_rfl

private theorem promote_ct_eq_loop_placed_wp [LibsignalPlacement]
    {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (bs : List (BitVec 8)) (hne : bs ≠ []) (hlt : bs.length < 2 ^ 64)
    (serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (blkPl_50).base + 0x80#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs.length)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H)
      ((blkPl_50).base + 0xb4#64) s
      ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs))
      (fun sf Pf =>
        Pf = ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs)) ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = 1#64 ∧
        sf.readReg64 .x23 = outPtr ∧
        sf.vregs = s.vregs) :=
  promote_ct_eq_loop_prog_wp_pl ((blkPC_50).rebase (blkPl_50).base H)
    ((blkPl_50).base + 0x80#64)
    ((blkPl_50).base + 0xb4#64)
    outPtr
    (fun b0 serPtr alicePtr s hpc hrun hx19 hx21 hx22 hx23 hx25 =>
      promote_ct_eq_loop_last_placed_wp h_bb b0 serPtr alicePtr outPtr s hpc hrun hx19 hx21 hx22 hx23 hx25)
    (fun b0 m hm_pos hm_lt serPtr alicePtr s hpc hrun hx19 hx21 hx22 hx23 hx25 =>
      promote_ct_eq_loop_step_placed_wp h_bb b0 m hm_pos hm_lt serPtr alicePtr outPtr s hpc hrun hx19 hx21 hx22 hx23 hx25)
    bs hne hlt serPtr alicePtr s hpc hrun hx19 hx21 hx22 hx23 hx25

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
theorem promote_matching_session_raw_placed_ok [LibsignalPlacement]
    {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H)
      (blkPl_50).base
      promoteMatchingSessionRawSpec := by
  refine subroutine_ok_of_sepWP_init
    fun ⟨recPtr, locCap, alicePtr, sessVer, msgVer, serPtr, serBytes, outPtr⟩ R s0
      hpc hrun hpre hsp_align => ?_
  dsimp only [promoteMatchingSessionRawSpec] at hpre ⊢
  refine ⟨_, hpre, ?_⟩
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
  obtain ⟨hx0, hx1, hx2, hx3, hx8, hcap, hver, hlen⟩ := hpure
  apply SepWP.seq
  · exact SepWP.frame_auto (promote_prologue_placed_wp s0 recPtr locCap alicePtr serPtr outPtr sessVer msgVer
      hpc hrun hsp_align' hx0 hx1 hx2 hx3 hx8 hcap hver)
  · intro s1 _ hpc1 hrun1 ⟨hent1, htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hvregs1⟩
    refine SepWP.weaken_pre hent1 ?_
    have hne : serBytes ≠ [] := by intro he; rw [he] at hlen; contradiction
    have hlt : serBytes.length < 2 ^ 64 := by omega
    have hx21_len : s1.readReg64 .x21 = BitVec.ofNat 64 serBytes.length := by
      rw [hlen]; exact hx21_1
    refine SepWP.bind_seq_readOnly
      (promote_ct_eq_loop_placed_wp h_bb serBytes hne hlt serPtr alicePtr outPtr s1
        hpc1 hrun1 hx19_1 hx21_len hx22_1 hx23_1 hx25_1)
      (by sep_focus) fun s2 hpc2 hrun2 ⟨htr2, hsp2, hx0_2, hx23_2, hvregs2⟩ => ?_
    apply SepWP.mono
    · exact SepWP.frame_auto (promote_epilogue_placed_wp s0 s2 outPtr hpc2 hrun2 hsp_align'
        (htr2.trans htr1) (hsp2.trans hsp1) hx0_2 hx23_2 (hvregs2.trans hvregs1))
    · intro sf _ _ _ ⟨hentf, htrf, hspf, hcsf⟩
      refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm, hspf, hcsf⟩
      refine Entails.trans hentf ?_
      rw [htrf]
      sep_frame
    · intro _ _ _ hf; exact hf

private theorem stackAt_promoteMatch_eq_pl (sp : BitVec 64) :
    stackAt sp promoteMatchingSessionMatchStack =
      (∃∗ w4a0 : BitVec 64, (sp - 1184#64) ↦₆₄ w4a0) ∗
      memRegion (sp - 1176#64) 40 ∗
      (∃∗ w470 : BitVec 64, (sp - 1136#64) ↦₆₄ w470) ∗
      memRegion (sp - 1128#64) 1032 ∗
      cells (sp - 96#64) 12 := by
  change memRegion (sp - 1184#64) 1184 = _
  rw [show (1184 : Nat) = 8 + (40 + (8 + (1032 + 96))) by decide,
    memRegion_split (sp - 1184#64) 8 _ (by decide),
    ProofLib.memRegion_eight (sp - 1184#64),
    show sp - 1184#64 + 8#64 = sp - 1176#64 by bv_omega,
    memRegion_split (sp - 1176#64) 40 _ (by decide),
    show sp - 1176#64 + 40#64 = sp - 1136#64 by bv_omega,
    memRegion_split (sp - 1136#64) 8 _ (by decide),
    ProofLib.memRegion_eight (sp - 1136#64),
    show sp - 1136#64 + 8#64 = sp - 1128#64 by bv_omega,
    memRegion_split (sp - 1128#64) 1032 96 (by decide),
    show sp - 1128#64 + 1032#64 = sp - 96#64 by bv_omega,
    show (96 : Nat) = 8 * 12 by decide,
    ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]

private theorem outRegion16_split_pl (outPtr : BitVec 64) :
    memRegion outPtr 16 =
      (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
      (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
      memRegion (outPtr + 9#64) 7 := by
  rw [show (16 : Nat) = 8 + (1 + 7) by decide,
    memRegion_split outPtr 8 (1 + 7) (by decide),
    ProofLib.memRegion_eight outPtr,
    memRegion_split (outPtr + 8#64) 1 7 (by decide),
    ProofLib.memRegion_one (outPtr + 8#64),
    show outPtr + 8#64 + 1#64 = outPtr + 9#64 by bv_omega]

private theorem pure_keep_pl {ψ φ : Prop} (h : ψ → φ) :
    (⌜ψ⌝ : SepProp) = ⌜φ⌝ ∗ ⌜ψ⌝ := by
  rw [pure_sepConj_pure]
  congr 1
  exact propext ⟨fun hψ => ⟨h hψ, hψ⟩, fun ⟨_, hψ⟩ => hψ⟩

private def vecGhostRest0_pl (A : RustAlloc) (v : BitVec 64) (vg : VecGhost) : SepProp :=
  ((v + 8#64) ↦₆₄ vg.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vg.bytes.length) ∗
  ⌜vg.bytes.length ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0⌝ ∗
  (if vg.cap = 0 then emp
   else A.live vg.ptr vg.cap.toNat 1 ∗ (vg.ptr ↦ₛ vg.bytes) ∗
     memRegion (vg.ptr + BitVec.ofNat 64 vg.bytes.length) (vg.cap.toNat - vg.bytes.length))

private theorem vecGhostAt_eq_split0_pl (A : RustAlloc) (v : BitVec 64) (vg : VecGhost) :
    vecGhostAt A vg v =
      ⌜vg.cap.toNat < 2 ^ 63⌝ ∗ (v ↦₆₄ vg.cap) ∗ vecGhostRest0_pl A v vg := by
  have hk := pure_keep_pl
    (ψ := vg.bytes.length ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0)
    (fun h => h.2.1)
  unfold vecGhostAt vecU8At vecHeader vecGhostRest0_pl
  conv_lhs => rw [hk]
  ac_rfl

private theorem vecGhostAt_restore0_pl (A : RustAlloc) (v : BitVec 64) (vg : VecGhost) :
    (v ↦₆₄ vg.cap) ∗ vecGhostRest0_pl A v vg = vecGhostAt A vg v := by
  unfold vecGhostAt vecU8At vecHeader vecGhostRest0_pl
  ac_rfl

private def vecGhostRestAlice_pl (A : RustAlloc) (v : BitVec 64) (vg : VecGhost) : SepProp :=
  (v ↦₆₄ vg.cap) ∗
  ⌜vg.bytes.length ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0⌝ ∗
  A.live vg.ptr vg.cap.toNat 1 ∗
  memRegion (vg.ptr + BitVec.ofNat 64 vg.bytes.length) (vg.cap.toNat - vg.bytes.length)

private theorem vecGhostAt_eq_split_alice_pl (A : RustAlloc) (v : BitVec 64) (vg : VecGhost)
    (serBytes : List (BitVec 8)) (heq : vg.bytes = serBytes) (hlen : serBytes.length = 33) :
    vecGhostAt A vg v =
      ((v + 8#64) ↦₆₄ vg.ptr) ∗ ((v + 16#64) ↦₆₄ 33#64) ∗
      (vg.ptr ↦ₛ serBytes) ∗ vecGhostRestAlice_pl A v vg := by
  unfold vecGhostAt vecU8At vecHeader vecGhostRestAlice_pl
  rw [heq, hlen]
  have hcongr :
      (⌜33 ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0⌝ ∗
        if vg.cap = 0 then emp
        else A.live vg.ptr vg.cap.toNat 1 ∗ (vg.ptr ↦ₛ serBytes) ∗
          memRegion (vg.ptr + BitVec.ofNat 64 33) (vg.cap.toNat - 33)) =
      (⌜33 ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0⌝ ∗
        (A.live vg.ptr vg.cap.toNat 1 ∗ (vg.ptr ↦ₛ serBytes) ∗
          memRegion (vg.ptr + BitVec.ofNat 64 33) (vg.cap.toNat - 33))) := by
    refine pure_sepConj_congr fun ⟨hle, _, _⟩ => ?_
    have hc : vg.cap ≠ 0#64 := by intro hc0; rw [hc0] at hle; simp at hle
    simp [hc]
  rw [hcongr]
  change _ = ((v + 8#64) ↦₆₄ vg.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 33) ∗ _
  ac_rfl

private def ssPureProp_pl (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Prop :=
  PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
  (match st.remoteIdentity with
   | none => G.remoteIk.bytes = []
   | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
  G.chains.length = st.receiverChains.length ∧
  G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
  G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)

private def ssMid1_pl (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  vecGhostAt A G.remoteIk (ss + asm64% ssRemoteIdentityOff) ∗
  vecU8At A (ss + asm64% ssRootKeyOff) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
  vecAt A (asm% chainSize) (asm% chainAlign) (chainAt A) (ss + asm64% ssReceiverChainsOff)
    G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains)

private def ssMid2_pl (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  vecU8At A (ss + asm64% ssPqRatchetStateOff) G.pq.cap G.pq.ptr st.pqRatchetState ∗
  optSenderChainAt A (ss + asm64% ssSenderChainOff) G.sender st.senderChain ∗
  optTailVecAt A (asm% pendingPreKeySize) (ss + asm64% ssPendingPreKeyOff) G.pending ∗
  optTailVecAt A (asm% pendingKyberPreKeySize) (ss + asm64% ssPendingKyberPreKeyOff) G.kyber

private def ssTail_pl (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ((ss + asm64% ssPreviousCounterOff) ↦₃₂ st.previousCounter) ∗
  ((ss + asm64% ssRegistrationIdsOff) ↦ₛ G.regIds)

private theorem sessionStateAt_eq_chunks_pl (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      ⌜ssPureProp_pl G st⌝ ∗
      vecGhostAt A G.localIk ss ∗
      ssMid1_pl A ss G st ∗
      vecGhostAt A G.alice (ss + 0x60#64) ∗
      ssMid2_pl A ss G st ∗
      ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
      ssTail_pl ss G st := by
  unfold sessionStateAt ssPureProp_pl ssMid1_pl ssMid2_pl ssTail_pl
  simp only [sepConj_assoc]
  rfl

private def sessPureProp_pl (G : SessionGhost) (s : Session (List (BitVec 8))) : Prop :=
  PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
  G.alice.bytes = s.aliceBaseKey ∧
  G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
  (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat

private theorem sessionAt_eq_chunks_pl (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) :
    sessionStateReprAt A ss G s =
      ⌜G.alice.bytes = s.aliceBaseKey⌝ ∗
      ⌜sessPureProp_pl G s⌝ ∗
      sessionStateAt A ss G s.state := by
  change ⌜sessPureProp_pl G s⌝ ∗ sessionStateAt A ss G s.state = _
  conv_lhs => rw [pure_keep_pl (ψ := sessPureProp_pl G s) (fun h => h.2.2.1)]
  rw [sepConj_assoc]

private theorem sessionAt_restore_chunks_pl (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) :
    ⌜sessPureProp_pl G s⌝ ∗ sessionStateAt A ss G s.state = sessionStateReprAt A ss G s :=
  rfl

private def promoteMatchFrame_pl (A : RustAlloc) (recPtr outPtr sp : BitVec 64)
    (g : RecordGhost) (G : SessionGhost) (s : Session (List (BitVec 8))) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) recPtr g.prevCap g.prevPtr [] ∗
  ⌜sessPureProp_pl G s⌝ ∗
  ⌜ssPureProp_pl G s.state⌝ ∗
  vecGhostRest0_pl A (recPtr + 0x18#64) G.localIk ∗
  ssMid1_pl A (recPtr + 0x18#64) G s.state ∗
  vecGhostRestAlice_pl A (recPtr + 0x78#64) G.alice ∗
  ssMid2_pl A (recPtr + 0x18#64) G s.state ∗
  ssTail_pl (recPtr + 0x18#64) G s.state ∗
  memRegion (outPtr + 9#64) 7 ∗
  memRegion (sp - 1176#64) 40 ∗
  memRegion (sp - 1128#64) 1032

set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
private theorem promoteMatch_pre_entails_pl (A : RustAlloc) (x : PromoteMatchGhost)
    (G : SessionGhost) (s0 : State)
    (hgc : x.g.cur = some G)
    (hx0 : s0.readReg64 .x0 = x.recPtr)
    (hx1 : s0.readReg64 .x1 = x.msgVer.zeroExtend 64)
    (hx2 : s0.readReg64 .x2 = x.serPtr)
    (hx3 : s0.readReg64 .x3 = 33#64)
    (hx8 : s0.readReg64 .x8 = x.outPtr)
    (hcur : x.r.currentSession = some x.s)
    (hver : x.s.state.version = x.msgVer.zeroExtend 32)
    (halice : x.s.aliceBaseKey = x.serBytes)
    (hlen : x.serBytes.length = 33) :
    sessionRecordAt A x.recPtr x.g x.r ∗
      (x.serPtr ↦ₛ x.serBytes) ∗
      memRegion x.outPtr 16 ∗
      stackAt s0.sp promoteMatchingSessionMatchStack ⊢
    promoteMatchingSessionRawSpec.pre
      ⟨x.recPtr, G.localIk.cap, G.alice.ptr, x.s.state.sessionVersion,
       x.msgVer, x.serPtr, x.serBytes, x.outPtr⟩ s0 ∗
      promoteMatchFrame_pl A x.recPtr x.outPtr s0.sp x.g G x.s := by
  dsimp only [promoteMatchingSessionRawSpec, promoteMatchFrame_pl]
  simp only [sessionRecordAt, hgc, hcur,
    sessionAt_eq_chunks_pl A (x.recPtr + 0x18#64) G x.s,
    sessionStateAt_eq_chunks_pl A (x.recPtr + 0x18#64) G x.s.state,
    vecGhostAt_eq_split0_pl A (x.recPtr + 0x18#64) G.localIk,
    outRegion16_split_pl x.outPtr, stackAt_promoteMatch_eq_pl s0.sp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.trans (Entails.of_eq (by sep_focus : _ =
    (⌜G.alice.bytes = x.s.aliceBaseKey⌝ ∗ ⌜G.localIk.cap.toNat < 2 ^ 63⌝) ∗ _)) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hal_g => Entails.pure_left fun hcap => ?_
  have hal_eq : G.alice.bytes = x.serBytes := hal_g.trans halice
  have hver' : (if x.s.state.sessionVersion = 0#32 then 2#32 else x.s.state.sessionVersion) =
      x.msgVer.zeroExtend 32 := hver
  simp only [vecGhostAt_eq_split_alice_pl A (x.recPtr + 0x78#64) G.alice x.serBytes hal_eq hlen,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx8, hcap, hver', hlen⟩ ?_
  exact Entails.of_eq (by ac_rfl)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
private theorem promoteMatch_post_entails_pl (A : RustAlloc) (x : PromoteMatchGhost)
    (G : SessionGhost) (s0 sf : State)
    (hgc : x.g.cur = some G)
    (hcur : x.r.currentSession = some x.s)
    (halice : x.s.aliceBaseKey = x.serBytes)
    (hlen : x.serBytes.length = 33) :
    promoteMatchingSessionRawSpec.post
      ⟨x.recPtr, G.localIk.cap, G.alice.ptr, x.s.state.sessionVersion,
       x.msgVer, x.serPtr, x.serBytes, x.outPtr⟩ s0 sf ∗
      promoteMatchFrame_pl A x.recPtr x.outPtr s0.sp x.g G x.s ⊢
    (promoteMatchingSessionMatchSpec A).post x s0 sf := by
  dsimp only [promoteMatchingSessionRawSpec, promoteMatchingSessionMatchSpec, promoteMatchFrame_pl]
  simp only [sepConj_assoc]
  refine Entails.trans (Entails.of_eq (by sep_focus : _ = ⌜sessPureProp_pl G x.s⌝ ∗ _)) ?_
  refine Entails.pure_left fun hsess => ?_
  have hal_eq : G.alice.bytes = x.serBytes := hsess.2.2.1.trans halice
  simp only [sessionRecordAt, hgc, hcur,
    ← sessionAt_restore_chunks_pl A (x.recPtr + 0x18#64) G x.s,
    sessionStateAt_eq_chunks_pl A (x.recPtr + 0x18#64) G x.s.state,
    ← vecGhostAt_restore0_pl A (x.recPtr + 0x18#64) G.localIk,
    vecGhostAt_eq_split_alice_pl A (x.recPtr + 0x78#64) G.alice x.serBytes hal_eq hlen,
    stackAt_promoteMatch_eq_pl s0.sp,
    pure_sepConj_of_true hsess,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem promote_matching_session_match_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H)
      (blkPl_50).base
      (promoteMatchingSessionMatchSpec A) := by
  refine subroutine_ok_refine_frame (promote_matching_session_raw_placed_ok h_bb) ?_
  intro x R s0 hpre
  have hpre' : s0.mem ⊨
      ⌜s0.readReg64 .x0 = x.recPtr ∧
       s0.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
       s0.readReg64 .x2 = x.serPtr ∧
       s0.readReg64 .x3 = 33#64 ∧
       s0.readReg64 .x8 = x.outPtr ∧
       x.r.currentSession = some x.s ∧
       x.s.state.version = x.msgVer.zeroExtend 32 ∧
       x.s.aliceBaseKey = x.serBytes ∧
       x.serBytes.length = 33⌝ ∗
      ((sessionRecordAt A x.recPtr x.g x.r ∗
        (x.serPtr ↦ₛ x.serBytes) ∗
        memRegion x.outPtr 16 ∗
        stackAt s0.sp promoteMatchingSessionMatchStack) ∗ R) := by
    dsimp only [promoteMatchingSessionMatchSpec] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx8, hcur, hver, halice, hlen⟩, hpre_sp⟩ := hpre'
  cases hgc : x.g.cur with
  | none =>
    exfalso
    have hfalse : s0.mem ⊨ ⌜False⌝ ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) x.recPtr x.g.prevCap x.g.prevPtr [] ∗
         (x.serPtr ↦ₛ x.serBytes) ∗ memRegion x.outPtr 16 ∗
         stackAt s0.sp promoteMatchingSessionMatchStack ∗ R) := by
      simp only [sessionRecordAt, hgc, hcur] at hpre_sp
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre_sp
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1
  | some G =>
    refine ⟨⟨x.recPtr, G.localIk.cap, G.alice.ptr, x.s.state.sessionVersion,
             x.msgVer, x.serPtr, x.serBytes, x.outPtr⟩,
            promoteMatchFrame_pl A x.recPtr x.outPtr s0.sp x.g G x.s, ?_, ?_⟩
    · rw [← sepConj_assoc]
      exact Satisfies.mono
        (sepConj_mono_left
          (promoteMatch_pre_entails_pl A x G s0 hgc hx0 hx1 hx2 hx3 hx8 hcur hver halice hlen))
        hpre_sp
    · intro sf hpost
      rw [← sepConj_assoc] at hpost
      exact Satisfies.mono
        (sepConj_mono_left (promoteMatch_post_entails_pl A x G s0 sf hgc hcur halice hlen))
        hpost

theorem promote_matching_session_match_placed_ok_at [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 50)
      (withLsCodeLoaded lsmpl (promoteMatchingSessionMatchSpec A)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (entry := lsmpl.base 50)
    (subroutine_ok_withLsCodeLoaded_of_plain (promote_matching_session_match_placed_ok h_bb)) hi

theorem promote_matching_session_match_placed_cl_ok_at [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 50)
      (withLsCl lsmpl (promoteMatchingSessionMatchSpec A)) :=
  ls_subroutine_ok_cl_of_plain (callerProg := callerProg) (entry := lsmpl.base 50)
    (promote_matching_session_match_placed_ok h_bb) hi

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
