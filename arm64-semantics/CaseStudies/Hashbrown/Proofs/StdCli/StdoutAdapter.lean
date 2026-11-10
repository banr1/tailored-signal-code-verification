/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.StdoutWrite
public meta import CaseStudies.Hashbrown.Proofs.StdCli.StdoutWrite
public meta import ProofLib.SepLogic.Stack

/-!
# `StdoutLock::write_all` Non-Newline Path and `HbFmtWriter` Instance

Proves the non-newline path of `StdoutLock::write_all` over `C : HbCliLayout` and instantiates
`HbFmtWriter`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown

local macro "iAdrp " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr true $rd (adrpOff $pc $t))
local macro "iAddLo12 " rd:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.addSubImm .W64 .ADD $rd $rn (($t).truncate 12) false)
local macro "iLdr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W64 .X64 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.str .X64 $rt (.Offset $rn (pageLo12 $t)))
local macro "iBl " pc:term:arg t:term:arg : term => `(Instr.bl ($t - $pc))
local macro "iB " pc:term:arg t:term:arg : term => `(Instr.b ($t - $pc))


local macro "unpack_stdout_code " chunks:ident h:term : tactic => `(tactic| (
  have _hc := stdoutToStepFacts $h
  simp only [$chunks:ident, stdoutStepFacts, stdoutStepAcc, fetchAtAcc',
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

local macro "norm_jmp" : tactic =>
  `(tactic| conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel'])

local macro "unpack_cells " k:num : tactic => `(tactic| (
  try simp only [Nat.reduceMul]
  cells_unfold
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate $k (apply SepWP.exists_left; intro _)))

local macro "repack_cells" : tactic => `(tactic| (
  try simp only [Nat.reduceMul]
  cells_unfold
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  sep_entail))

attribute [local simp] cpuAux_writeReg64 cpuAux_writeReg32 cpuAux_writeReg
  cpuAux_setPState cpuAux_advancePC cpuAux_setPC cpuAux_setMem

local macro "unpack_cs " h:ident : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := $h)
local macro "close_cs" : tactic =>
  `(tactic| simp [CalleeSavedPreserved.iff_regs, Reg.fp, wp_norm, arm64_norm, *])
local macro "wp_a" : term => `(by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)


private theorem getD_ne_of_not_mem : ∀ {bs : List (BitVec 8)} {i : Nat} {x : BitVec 8},
    i < bs.length → x ∉ bs → bs.getD i 0#8 ≠ x
  | [], _, _, hi, _ => by simp at hi
  | hd :: _, 0, _, _, hnot => fun h => by
      change hd = _ at h; subst h; exact hnot (List.mem_cons_self ..)
  | hd :: tl, n + 1, x, hi, hnot =>
      @getD_ne_of_not_mem tl n x (Nat.lt_of_succ_lt_succ hi)
        (fun hm => hnot (List.mem_cons_of_mem hd hm))

private theorem zext32_bne_0a {x : BitVec 8} (hx : x ≠ 0x0a#8) :
    (BitVec.zeroExtend 32 x != 0x0a#32) = true := by
  have hxlt := x.isLt
  rw [bne_iff_ne]; intro heq; apply hx; apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat heq; simp at this
  change x.toNat = 10; omega

private theorem bv64_ofNat_beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [decide_eq_false h, beq_eq_false_iff_ne]; intro heq
    have := congrArg BitVec.toNat heq; simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact h this

private theorem tailScan_noNl_wp {P : Program} {C : HbCliLayout}
    {target_pc slicePtr : BitVec 64} {bs : List (BitVec 8)}
    (hc : HbStdoutCode P C) (r : Nat) (hbs_hi : bs.length ≤ 20) (hnoNl : 0x0a#8 ∉ bs) :
    ∀ (rem k : Nat) (st : State) {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp},
      r + rem + k ≤ bs.length →
      st.pc = C.memrchrAddr + 0x50#64 → st.status = .Running →
      st.readReg64 .x1 = slicePtr →
      st.readReg64 .x8 = BitVec.ofNat 64 (k + rem) →
      st.readReg32 .x9 = 0x0a#32 →
      st.readReg64 .x11 = BitVec.ofNat 64 k →
      (1 ≤ rem → st.readReg64 .x12 = slicePtr + BitVec.ofNat 64 (r + rem - 1)) →
      (∀ sf : State,
        sf.pc = C.memrchrAddr + 0x78#64 → sf.status = .Running →
        sf.sp = st.sp → CalleeSavedPreserved st sf →
        sf.readReg64 .x0 = st.readReg64 .x0 →
        sf.readReg64 .x1 = slicePtr →
        sf.readReg64 .x2 = st.readReg64 .x2 →
        sf.readReg64 .x9 = st.readReg64 .x9 →
        sf.readReg64 .x10 = st.readReg64 .x10 →
        sf.fs = st.fs → sf.tpidrEl0 = st.tpidrEl0 → sf.trace = st.trace →
        SepWP (P.withSvc hbStdioSvc) target_pc sf ((slicePtr ↦ₛ bs) ∗ F) post oom) →
      SepWP (P.withSvc hbStdioSvc) target_pc st ((slicePtr ↦ₛ bs) ∗ F) post oom := by
  intro rem
  induction rem with
  | zero =>
    intro k st F post oom _ hpc hrun hx1 hx8 _ hx11 _ hnext
    have hcMr := (hc.withSvc hbStdioSvc).memrchr
    unpack_stdout_code hbMemrchrChunks hcMr
    have hx8' : st.readReg64 (.gpr 8#5) = BitVec.ofNat 64 k := by simpa using hx8
    have hx11' : st.readReg64 (.gpr 11#5) = BitVec.ofNat 64 k := hx11
    wp_steps 2
    exact hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a (by close_cs)
      wp_a wp_a wp_a wp_a wp_a (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
  | succ rem ih =>
    intro k st F post oom hrem hpc hrun hx1 hx8 hw9 hx11 hx12 hnext
    have hcMr := (hc.withSvc hbStdioSvc).memrchr
    unpack_stdout_code hbMemrchrChunks hcMr
    have hx8' : st.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (k + (rem + 1)) := hx8
    have hw9' : BitVec.truncate 32 (st.readReg64 (.gpr 9#5)) = 0x0a#32 := hw9
    have hx11' : st.readReg64 (.gpr 11#5) = BitVec.ofNat 64 k := hx11
    have hx12' : st.readReg64 (.gpr 12#5) = slicePtr + BitVec.ofNat 64 (r + rem) := by
      simpa using hx12 (by omega)
    have hneq : (BitVec.ofNat 64 (k + (rem + 1)) == BitVec.ofNat 64 k) = false := by
      rw [bv64_ofNat_beq_ofNat (by omega) (by omega)]; exact decide_eq_false (by omega)
    have hadd11 : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
    have hbne : (BitVec.zeroExtend 32 (bs.getD (r + rem) 0#8) != 0x0a#32) = true :=
      zext32_bne_0a (getD_ne_of_not_mem (by omega) hnoNl)
    have hbne' : (BitVec.zeroExtend 32 (bs.getD (Nat.add r rem) 0#8) != 0x0a#32) = true := hbne
    wp_steps 6
    refine ih (k + 1) _ (by omega) wp_a
      (by simp [wp_norm, arm64_norm, hrun]) wp_a
      (by simp only [wp_norm, arm64_norm, hx8']; rw [show k + (rem + 1) = (k + 1) + rem by omega])
      wp_a wp_a
      (fun hpos => by
        simp only [wp_norm, arm64_norm]
        have hsub : BitVec.ofNat 64 (r + rem) - 1#64 = BitVec.ofNat 64 (r + rem - 1) :=
          bv64_sub_ofNat (by omega)
        rw [← hsub]; bv_lin)
      fun sf hpcf hrunf hspf hcsf hx0f hx1f hx2f hx9f hx10f hfsf htidf htrf =>
        hnext sf hpcf hrunf (by simpa [wp_norm, arm64_norm] using hspf)
          (by unpack_cs hcsf; close_cs)
          (by simpa [wp_norm, arm64_norm] using hx0f)
          hx1f
          (by simpa [wp_norm, arm64_norm] using hx2f)
          (by simpa [wp_norm, arm64_norm] using hx9f)
          (by simpa [wp_norm, arm64_norm] using hx10f)
          (by simpa [wp_norm, arm64_norm] using hfsf)
          (by simpa [wp_norm, arm64_norm] using htidf)
          (by simpa [wp_norm, arm64_norm] using htrf)

private theorem headScan_noNl_wp {P : Program} {C : HbCliLayout}
    {target_pc slicePtr : BitVec 64} {bs : List (BitVec 8)}
    (hc : HbStdoutCode P C) (hbs_hi : bs.length ≤ 20) (hnoNl : 0x0a#8 ∉ bs) :
    ∀ (m : Nat) (st : State) {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp},
      m ≤ bs.length →
      st.pc = C.memrchrAddr + 0xd8#64 → st.status = .Running →
      st.readReg64 .x8 = BitVec.ofNat 64 m →
      st.readReg32 .x9 = 0x0a#32 →
      st.readReg64 .x10 = slicePtr - 1#64 →
      (∀ sf : State,
        sf.pc = C.memrchrAddr + 0xf8#64 → sf.status = .Running →
        sf.sp = st.sp → CalleeSavedPreserved st sf →
        sf.fs = st.fs → sf.tpidrEl0 = st.tpidrEl0 → sf.trace = st.trace →
        SepWP (P.withSvc hbStdioSvc) target_pc sf ((slicePtr ↦ₛ bs) ∗ F) post oom) →
      SepWP (P.withSvc hbStdioSvc) target_pc st ((slicePtr ↦ₛ bs) ∗ F) post oom := by
  intro m
  induction m with
  | zero =>
    intro st F post oom _ hpc hrun hx8 _ _ hnext
    have hcMr := (hc.withSvc hbStdioSvc).memrchr
    unpack_stdout_code hbMemrchrChunks hcMr
    have hx8' : st.readReg64 (.gpr 8#5) = 0#64 := hx8
    wp_steps 1
    exact hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a (by close_cs)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
  | succ m ih =>
    intro st F post oom hm_le hpc hrun hx8 hw9 hx10 hnext
    have hcMr := (hc.withSvc hbStdioSvc).memrchr
    unpack_stdout_code hbMemrchrChunks hcMr
    have hx8' : st.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (m + 1) := hx8
    have hw9' : BitVec.truncate 32 (st.readReg64 (.gpr 9#5)) = 0x0a#32 := hw9
    have hx10' : st.readReg64 (.gpr 10#5) = slicePtr - 1#64 := hx10
    have hnz : (BitVec.ofNat 64 (m + 1) == 0#64) = false := by
      rw [bv64_ofNat_beq_zero (by omega)]; exact decide_eq_false (by omega)
    have hsub8 : BitVec.ofNat 64 (m + 1) - 1#64 = BitVec.ofNat 64 m := bv64_sub_ofNat (by omega)
    have hbne : (BitVec.zeroExtend 32 (bs.getD m 0#8) != 0x0a#32) = true :=
      zext32_bne_0a (getD_ne_of_not_mem (by omega) hnoNl)
    have hbne' : (BitVec.zeroExtend 32 (bs.getD (Nat.sub (m + 1) 1) 0#8) != 0x0a#32) = true := hbne
    wp_steps 6
    refine ih _ (by omega) wp_a
      (by simp [wp_norm, arm64_norm, hrun]) wp_a wp_a wp_a
      fun sf hpcf hrunf hspf hcsf hfsf htidf htrf =>
        hnext sf hpcf hrunf (by simpa [wp_norm, arm64_norm] using hspf)
          (by unpack_cs hcsf; close_cs)
          (by simpa [wp_norm, arm64_norm] using hfsf)
          (by simpa [wp_norm, arm64_norm] using htidf)
          (by simpa [wp_norm, arm64_norm] using htrf)

private theorem hbMemrchr_noNl_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp0 slicePtr : BitVec 64} {bs : List (BitVec 8)}
    (hc : HbStdoutCode P C) {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hbs_lo : 1 ≤ bs.length) (hbs_hi : bs.length ≤ 20) (hbs_noNl : 0x0a#8 ∉ bs)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ ((slicePtr ↦ₛ bs) ∗ stackAt sp0 16) ∗ (F ∗ R)))
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      sf.fs = s.fs → sf.tpidrEl0 = s.tpidrEl0 → sf.trace = s.trace →
      SepWP (P.withSvc hbStdioSvc) target_pc sf
        (((slicePtr ↦ₛ bs) ∗ stackAt sp0 16) ∗ F) post oom)
    (hpc : s.pc = C.memrchrAddr := by wp_arg)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp : s.sp = sp0 := by wp_arg) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc := by wp_arg)
    (hw0 : s.readReg32 .x0 = 0x0a#32 := by wp_arg)
    (hx1 : s.readReg64 .x1 = slicePtr := by wp_arg)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length := by wp_arg) :
    SepWP (P.withSvc hbStdioSvc) target_pc s Pre post oom := by
  subst hsp
  have hcMr := (hc.withSvc hbStdioSvc).memrchr
  unpack_stdout_code hbMemrchrChunks hcMr
  refine hbMemrchrEntry_to_3c_wp false hc hbs_lo hbs_hi hpc hrun hsp_align hlr hw0 hx1 hx2
    (by dsimp only [hbBytesSlice]; exact hpre)
    fun r b st0 hr_le hrb hpc0 hrun0 hsp0 hcs0 hx0_0 hx1_0 hx2_0 hx8_0 hx10_0 hfs0 htid0 htr0 => ?_
  dsimp only [hbBytesSlice]
  have hc8 : ∀ (m : Nat) (sd : State) (Pd : SepProp),
      m ≤ bs.length →
      sd.pc = C.memrchrAddr + 0xc8#64 → sd.status = .Running →
      sd.sp = s.sp - 16#64 →
      (sd.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
       sd.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
       sd.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
       sd.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
       sd.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
       sd.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
       sd.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
       sd.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
       sd.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
       sd.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
       calleeSavedVRegs sd = calleeSavedVRegs s) →
      sd.readReg64 .x1 = slicePtr →
      sd.readReg64 .x2 = BitVec.ofNat 64 bs.length →
      sd.readReg64 .x8 = BitVec.ofNat 64 m →
      sd.readReg32 .x9 = 0x0a#32 →
      sd.fs = s.fs → sd.tpidrEl0 = s.tpidrEl0 → sd.trace = s.trace →
      (∀ R, sd.mem ⊨ Pd ∗ R → sd.mem ⊨ (hbMemrchrSlots s ret_pc ∗ (slicePtr ↦ₛ bs) ∗ F) ∗ R) →
      SepWP (P.withSvc hbStdioSvc) target_pc sd Pd post oom := by
    intro m sd Pd hm_le hpcd hrund hspd hcsd hx1d hx2d hx8d hw9d hfsd htidd htrd hpred
    have hx1d' : sd.readReg64 (.gpr 1#5) = slicePtr := hx1d
    have hx2d' : sd.readReg64 (.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2d
    have hx8d' : sd.readReg64 (.gpr 8#5) = BitVec.ofNat 64 m := hx8d
    have hw9d' : BitVec.truncate 32 (sd.readReg64 (.gpr 9#5)) = 0x0a#32 := hw9d
    have hult_m : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 m) = false := by
      rw [bv64_ult_ofNat (by omega) (by omega)]; exact decide_eq_false (by omega)
    refine SepWP.weaken_pre_frame
      (P' := (slicePtr ↦ₛ bs) ∗ (hbMemrchrSlots s ret_pc ∗ F))
      (fun R hm => by have h := hpred R hm; exact (by sep_entail : _ → _) h) ?_
    wp_steps 4
    refine headScan_noNl_wp hc hbs_hi hbs_noNl m _ hm_le wp_a (by simp [wp_norm, arm64_norm, hrund])
      wp_a wp_a wp_a fun sh hpch hrunh hsph hcsh hfsh htidh htrh => ?_
    have hsph' : sh.sp = s.sp - 16#64 := by simpa [wp_norm, arm64_norm, hspd] using hsph
    have hsph_al : sh.spAligned = true := by
      simp only [State.spAligned, hsph']; exact s.spAligned_sub 16#64 hsp_align
    rcases hcsd with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
    unpack_cs hcsh
    dsimp only [hbMemrchrSlots]
    wp_steps 3
    refine SepWP.weaken_pre_frame
      (P' := ((slicePtr ↦ₛ bs) ∗ stackAt s.sp 16) ∗ F)
      (fun _ hm => by rw [stackAt_eq_cells s.sp 2]; exact (by repack_cells : _ → _) hm) ?_
    exact hnext _ wp_a (by simp [wp_norm, arm64_norm, hrunh]) wp_a (by close_cs)
      wp_a (by simp [wp_norm, arm64_norm, hfsh, hfsd])
      (by simp [wp_norm, arm64_norm, htidh, htidd]) (by simp [wp_norm, arm64_norm, htrh, htrd])
  have hsub_r : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 r = BitVec.ofNat 64 (bs.length - r) :=
    bv64_sub_ofNat hr_le
  have hcomm : BitVec.ofNat 64 bs.length + slicePtr = slicePtr + BitVec.ofNat 64 bs.length :=
    BitVec.add_comm _ _
  refine SepWP.weaken_pre_frame
    (P' := (slicePtr ↦ₛ bs) ∗ (hbMemrchrSlots s ret_pc ∗ F))
    (fun R hm => (by sep_entail : _ → _) hm) ?_
  wp_steps 5
  refine tailScan_noNl_wp hc r hbs_hi hbs_noNl (bs.length - r) 0 _ (by omega) wp_a
    (by simp [wp_norm, arm64_norm, hrun0]) wp_a wp_a
    wp_a wp_a
    (fun hpos => by
      simp only [wp_norm, arm64_norm]
      have hsub1 : BitVec.ofNat 64 bs.length - 1#64 = BitVec.ofNat 64 (bs.length - 1) :=
        bv64_sub_ofNat hbs_lo
      rw [show r + (bs.length - r) - 1 = bs.length - 1 by omega, ← hsub1]; bv_lin)
    fun s78 hpc78 hrun78 hsp78 hcs078 hx0_78 hx1_78 hx2_78 hx9_78 hx10_78 hfs78 htid78 htr78 => ?_
  have hx0_78' : s78.readReg64 (.gpr 0#5) = BitVec.ofNat 64 r := by
    simpa [wp_norm, arm64_norm, hx0_0] using hx0_78
  have hx1_78' : s78.readReg64 (.gpr 1#5) = slicePtr := hx1_78
  have hx2_78' : s78.readReg64 (.gpr 2#5) = BitVec.ofNat 64 bs.length := by
    simpa [wp_norm, arm64_norm, hx2_0] using hx2_78
  have hw9_78 : BitVec.truncate 32 (s78.readReg64 (.gpr 9#5)) = 0x0a#32 := by
    rw [show s78.readReg64 (.gpr 9#5) = _ from hx9_78]; simp [wp_norm, arm64_norm]
  have hx10_78' : s78.readReg64 (.gpr 10#5) = BitVec.ofNat 64 b := by
    simpa [wp_norm, arm64_norm, hx10_0] using hx10_78
  have hcs78 :
      s78.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      s78.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
      s78.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
      s78.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
      s78.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
      s78.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
      s78.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
      s78.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
      s78.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
      s78.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
      calleeSavedVRegs s78 = calleeSavedVRegs s := by
    rcases hcs0 with ⟨_, _, _, _, _, _, _, _, _, _, _⟩; unpack_cs hcs078
    exact ⟨by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm, *]⟩
  wp_steps 6
  rcases hrb with rfl | ⟨hb7, rfl, h16⟩
  · have hule_rr : BitVec.ule (BitVec.ofNat 64 r) (BitVec.ofNat 64 r) = true := by simp [BitVec.ule]
    wp_steps 2
    exact hc8 r _ _ hr_le wp_a (by simp [wp_norm, arm64_norm, hrun78])
      (by simp [wp_norm, arm64_norm, hsp78, hsp0])
      (by rcases hcs78 with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
          exact ⟨wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a,
                 by simp [wp_norm, arm64_norm, *]⟩)
      wp_a wp_a wp_a (by simp [wp_norm, arm64_norm, hw9_78])
      (by simp [wp_norm, arm64_norm, hfs78, hfs0]) (by simp [wp_norm, arm64_norm, htid78, htid0])
      (by simp [wp_norm, arm64_norm, htr78, htr0]) (fun R hm => by sep_frame)
  · have hule16 : BitVec.ule (BitVec.ofNat 64 (b + 16)) (BitVec.ofNat 64 b) = false := by
      rw [bv64_ule_ofNat (by omega) (by omega)]; exact decide_eq_false (by omega)
    have hsub16 : BitVec.ofNat 64 (b + 16) - 16#64 = BitVec.ofNat 64 b := bv64_sub_ofNat (by omega)
    wp_steps 14
    split
    · have hule_bb : BitVec.ule (BitVec.ofNat 64 b) (BitVec.ofNat 64 b) = true := by simp [BitVec.ule]
      wp_steps 3
      exact hc8 b _ _ (by omega) wp_a (by simp [wp_norm, arm64_norm, hrun78])
        (by simp [wp_norm, arm64_norm, hsp78, hsp0])
        (by rcases hcs78 with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
            exact ⟨wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a,
                   by simp [wp_norm, arm64_norm, *]⟩)
        wp_a wp_a wp_a (by simp [wp_norm, arm64_norm, hw9_78])
        (by simp [wp_norm, arm64_norm, hfs78, hfs0]) (by simp [wp_norm, arm64_norm, htid78, htid0])
        (by simp [wp_norm, arm64_norm, htr78, htr0]) (fun R hm => by sep_frame)
    · exact hc8 (b + 16) _ _ hr_le wp_a (by simp [wp_norm, arm64_norm, hrun78])
        (by simp [wp_norm, arm64_norm, hsp78, hsp0])
        (by rcases hcs78 with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
            exact ⟨wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a,
                   by simp [wp_norm, arm64_norm, *]⟩)
        wp_a wp_a wp_a (by simp [wp_norm, arm64_norm, hw9_78])
        (by simp [wp_norm, arm64_norm, hfs78, hfs0]) (by simp [wp_norm, arm64_norm, htid78, htid0])
        (by simp [wp_norm, arm64_norm, htr78, htr0]) (fun R hm => by sep_frame)

private theorem hbStdoutLockWriteAll_noNl_stdioSvc_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp0 ptrSlot g bufPtr slicePtr : BitVec 64} {buffered bs : List (BitVec 8)}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C)
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hbs_lo : 1 ≤ bs.length) (hbs_hi : bs.length ≤ 20) (hbs_noNl : 0x0a#8 ∉ bs)
    (hbuf_hi : buffered.length ≤ 1024) (hbuf_noNl : 0x0a#8 ∉ buffered)
    (hbuf_va : bufPtr.toNat + 1024 ≤ Arm64.USER_VA_LIMIT)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ ((ptrSlot ↦₆₄ g) ∗ hbStdoutRefCell C g bufPtr buffered ∗ (slicePtr ↦ₛ bs) ∗
        stackAt sp0 256) ∗ (F ∗ R)))
    (hnext : ∀ (fl newBuf : List (BitVec 8)) (sf : State),
      fl ++ newBuf = buffered ++ bs → newBuf.length ≤ 1024 → 0x0a#8 ∉ newBuf →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 → sf.fs = s.fs → sf.tpidrEl0 = s.tpidrEl0 →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stdout fl →
      SepWP (P.withSvc hbStdioSvc) target_pc sf
        (((ptrSlot ↦₆₄ g) ∗ hbStdoutRefCell C g bufPtr newBuf ∗ (slicePtr ↦ₛ bs) ∗ stackAt sp0 256) ∗ F) post oom)
    (hpc : s.pc = C.stdoutLockWriteAllAddr := by wp_arg)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp : s.sp = sp0 := by wp_arg) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc := by wp_arg)
    (hx0 : s.readReg64 .x0 = ptrSlot := by wp_arg) (hx1 : s.readReg64 .x1 = slicePtr := by wp_arg)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length := by wp_arg) :
    SepWP (P.withSvc hbStdioSvc) target_pc s Pre post oom := by
  subst hsp
  have hcLw := (hc.withSvc hbStdioSvc).stdoutLockWriteAll
  unpack_stdout_code hbStdoutLockWriteAllChunks hcLw
  refine hbStdoutLockEntry_to_34_wp false hc hpc hrun hsp_align hlr hx0 hx1 hx2
    (by dsimp only [hbBytesSlice]; exact hpre)
    fun vPad st0 hpc0 hrun0 hsp0 hlr0 hcs0 hx19_0 hx20_0 hx22_0 hw0_0 hx1_0 hx2_0 hfs0 htid0 htr0 => ?_
  dsimp only [hbBytesSlice]
  have hbc : ∀ (sb : State) (Pb : SepProp),
      sb.pc = C.stdoutLockWriteAllAddr + 0xbc#64 → sb.status = .Running →
      sb.sp = s.sp - 64#64 →
      (sb.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
       sb.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
       sb.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
       sb.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
       sb.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
       calleeSavedVRegs sb = calleeSavedVRegs s) →
      sb.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bs.length →
      sb.readReg64 (.gpr 20#5) = slicePtr →
      sb.readReg64 (.gpr 21#5) = BitVec.ofNat 64 buffered.length →
      sb.readReg64 (.gpr 22#5) = g →
      sb.fs = s.fs → sb.tpidrEl0 = s.tpidrEl0 → sb.trace = s.trace →
      (∀ R, sb.mem ⊨ Pb ∗ R → sb.mem ⊨ (hbStdoutLockSlots s ret_pc vPad ∗ stackAt (s.sp - 64#64) 192 ∗
        (ptrSlot ↦₆₄ g) ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
        ((g + 0x10#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        hbBufWriterState (g + 0x18#64) bufPtr 0#8 buffered ∗ (slicePtr ↦ₛ bs) ∗ F) ∗ R) →
      SepWP (P.withSvc hbStdioSvc) target_pc sb Pb post oom := by
    intro sb Pb hpcb hrunb hspb hcsb hx19b hx20b hx21b hx22b hfsb htidb htrb hpreb
    have hspb_al : sb.spAligned = true := by
      simp only [State.spAligned, hspb]; exact s.spAligned_sub 64#64 hsp_align
    have hsub_cap : 1024#64 - BitVec.ofNat 64 buffered.length = BitVec.ofNat 64 (1024 - buffered.length) :=
      bv64_sub_ofNat hbuf_hi
    refine SepWP.weaken_pre_frame
      (P' := hbStdoutLockSlots s ret_pc vPad ∗ stackAt (s.sp - 64#64) 192 ∗
        (ptrSlot ↦₆₄ g) ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
        ((g + 0x10#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        hbBufWriterState (g + 0x18#64) bufPtr 0#8 buffered ∗ (slicePtr ↦ₛ bs) ∗ F)
      (fun R hm => by have h := hpreb R hm; exact (by sep_entail : _ → _) h) ?_
    dsimp only [hbBufWriterState]
    wp_steps
    by_cases hfit : bs.length < 1024 - buffered.length
    · have hule : BitVec.ule (BitVec.ofNat 64 (1024 - buffered.length)) (BitVec.ofNat 64 bs.length) = false := by
        rw [bv64_ule_ofNat (by omega) (by omega)]; exact decide_eq_false (by omega)
      rw [hule]; simp only [Bool.false_eq_true, ↓reduceIte]
      wp_steps; norm_jmp
      refine call_hbMemcpy false hMem (sp0 := s.sp - 64#64)
        (dst := bufPtr + BitVec.ofNat 64 buffered.length) (src := slicePtr) (bs := bs)
        (ret_pc := C.stdoutLockWriteAllAddr + 0xe0#64) (by omega)
        (fun R hm => by
          rw [memRegion_split_le (bufPtr + BitVec.ofNat 64 buffered.length) bs.length
            (1024 - buffered.length) (by omega) (by omega)] at hm
          dsimp only [hbBytesSlice]; sep_frame)
        (fun sc hpcc hrunc hspc hcsbc hx0c hstdbc => ?_)
      have hspc_al : sc.spAligned = true := by
        simp only [State.spAligned, hspc]; exact s.spAligned_sub 64#64 hsp_align
      have hx19c : sc.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bs.length := by rw [hcsbc.1]; exact wp_a
      have hx21c : sc.readReg64 (.gpr 21#5) = BitVec.ofNat 64 buffered.length := by rw [hcsbc.2.2.1]; exact wp_a
      have hx22c : sc.readReg64 (.gpr 22#5) = g := by rw [hcsbc.2.2.2.1]; exact wp_a
      wp_steps 4
      refine hbStdoutLockEpilogue_14c_wp (ptrSlot := ptrSlot) (g := g) (bufPtr := bufPtr) (slicePtr := slicePtr)
        (newBuf := buffered ++ bs) (bs := bs) (fl := [])
        false hc wp_a (by simp [wp_norm, arm64_norm, hrunc]) wp_a hsp_align
        (by rcases hcsb with ⟨_, _, _, _, _, _⟩; unpack_cs hcsbc
            exact ⟨wp_a, wp_a, wp_a, wp_a, wp_a, by simp [wp_norm, arm64_norm, *]⟩)
        wp_a wp_a (by simp [wp_norm, arm64_norm, hstdbc.1, hfsb])
        (by simp [wp_norm, arm64_norm, hstdbc.2.2.1, htidb])
        (by simp [wp_norm, arm64_norm, hstdbc.2.1, htrb, TraceEvent.ofBytes])
        (fun R hm => by
          dsimp only [hbBufWriterState, hbBytesSlice] at hm ⊢
          rw [List.length_append, pointsToBytes_append, BitVec.ofNat_add, ← BitVec.add_assoc,
              show 1024 - (buffered.length + bs.length) = 1024 - buffered.length - bs.length by omega]
          sep_frame)
        fun sf hpcf hrunf hspf hcsf hx0f hfsf htidf htrf => ?_
      dsimp only [hbBytesSlice]
      exact hnext [] (buffered ++ bs) sf rfl (by simp; omega)
        (by simp [List.mem_append, hbuf_noNl, hbs_noNl]) hpcf hrunf hspf hcsf hx0f hfsf htidf htrf
    · have hule : BitVec.ule (BitVec.ofNat 64 (1024 - buffered.length)) (BitVec.ofNat 64 bs.length) = true := by
        rw [bv64_ule_ofNat (by omega) (by omega)]; exact decide_eq_true (by omega)
      rw [hule]; simp only [↓reduceIte]
      wp_steps; norm_jmp
      refine hbBufWriterWriteAllCold_stdioSvc_wp false hc hcSys hMem hMemmove hbs_lo (by omega) hbuf_hi hbuf_va
        (sp0 := s.sp - 64#64) (bwPtr := g + 0x18#64) (bufPtr := bufPtr) (slicePtr := slicePtr)
        (buffered := buffered) (bs := bs) (ret_pc := C.stdoutLockWriteAllAddr + 0x188#64)
        (fun R hm => by dsimp only [hbBufWriterState, hbBytesSlice]; sep_frame)
        (fun sc hpcc hrunc hspc hcsbc hx0c hfsc htidc htrc => ?_)
      wp_steps 1
      refine hbStdoutLockEpilogue_14c_wp (ptrSlot := ptrSlot) (g := g) (bufPtr := bufPtr) (slicePtr := slicePtr)
        (newBuf := if bs.length ≤ 1024 - buffered.length then buffered ++ bs else bs) (bs := bs)
        (fl := if bs.length ≤ 1024 - buffered.length then [] else buffered)
        false hc wp_a (by simp [wp_norm, arm64_norm, hrunc]) wp_a hsp_align
        (by rcases hcsb with ⟨_, _, _, _, _, _⟩; unpack_cs hcsbc
            exact ⟨wp_a, wp_a, wp_a, wp_a, wp_a, by simp [wp_norm, arm64_norm, *]⟩)
        (by rw [State.readReg64_setPC, hx0c]) (by rw [State.readReg64_setPC, hcsbc.2.2.2.1]; exact wp_a)
        (by simp [wp_norm, arm64_norm, hfsc, hfsb]) (by simp [wp_norm, arm64_norm, htidc, htidb])
        (by simp [wp_norm, arm64_norm, htrc, htrb])
        (fun R hm => by dsimp only [hbBytesSlice] at hm ⊢; sep_frame)
        fun sf hpcf hrunf hspf hcsf hx0f hfsf htidf htrf => ?_
      dsimp only [hbBytesSlice]
      exact hnext (if bs.length ≤ 1024 - buffered.length then [] else buffered)
        (if bs.length ≤ 1024 - buffered.length then buffered ++ bs else bs) sf
        (by split <;> simp) (by split <;> (try simp) <;> omega)
        (by split <;> simp [List.mem_append, hbuf_noNl, hbs_noNl])
        hpcf hrunf hspf hcsf hx0f hfsf htidf htrf
  have hsp0_al : st0.spAligned = true := by
    simp only [State.spAligned, hsp0]; exact s.spAligned_sub 64#64 hsp_align
  refine hbMemrchr_noNl_wp hc hbs_lo hbs_hi hbs_noNl (sp0 := s.sp - 64#64) (slicePtr := slicePtr) (bs := bs)
    (ret_pc := C.stdoutLockWriteAllAddr + 0x38#64)
    (fun R hm => by rw [show (192 : Nat) = 16 + 176 from rfl, stackAt_split 16 176] at hm; sep_frame)
    (fun s1 hpc1 hrun1 hsp1 hcs01 hx0_1 hfs1 htid1 htr1 => ?_)
    hpc0 hrun0 hsp0 hsp0_al hlr0 hw0_0 hx1_0 hx2_0
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1]; exact s.spAligned_sub 64#64 hsp_align
  have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
  have hx19_1 : s1.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bs.length := by rw [hcs01.1]; exact hx19_0
  have hx20_1 : s1.readReg64 (.gpr 20#5) = slicePtr := by rw [hcs01.2.1]; exact hx20_0
  have hx22_1 : s1.readReg64 (.gpr 22#5) = g := by rw [hcs01.2.2.2.1]; exact hx22_0
  have hcs1 :
      s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
      s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
      s1.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
      s1.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
      s1.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s := by
    rcases hcs0 with ⟨_, _, _, _, _, _⟩; unpack_cs hcs01
    exact ⟨by simp_all, by simp_all, by simp_all, by simp_all, by simp_all, by simp_all⟩
  refine SepWP.weaken_pre_frame
    (P' := hbStdoutLockSlots s ret_pc vPad ∗ stackAt (s.sp - 64#64) 192 ∗
      (ptrSlot ↦₆₄ g) ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
      ((g + 0x10#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      hbBufWriterState (g + 0x18#64) bufPtr 0#8 buffered ∗ (slicePtr ↦ₛ bs) ∗ F)
    (fun R hm => by rw [show (192 : Nat) = 16 + 176 from rfl, stackAt_split 16 176]; sep_entail) ?_
  dsimp only [hbBufWriterState]
  wp_steps 4
  by_cases hbuf0 : buffered = []
  · subst hbuf0
    simp only [List.length_nil, beq_self_eq_true, ↓reduceIte]
    exact hbc _ _ wp_a (by simp [wp_norm, arm64_norm, hrun1]) wp_a
      (by rcases hcs1 with ⟨_, _, _, _, _, _⟩
          exact ⟨wp_a, wp_a, wp_a, wp_a, wp_a, by simp [wp_norm, arm64_norm, *]⟩)
      wp_a wp_a wp_a wp_a
      (by simp [wp_norm, arm64_norm, hfs1, hfs0]) (by simp [wp_norm, arm64_norm, htid1, htid0])
      (by simp [wp_norm, arm64_norm, htr1, htr0])
      (fun R hm => by dsimp only [hbBufWriterState, List.length_nil]; sep_frame)
  · have hbuf_pos : 1 ≤ buffered.length := List.length_pos_iff.mpr hbuf0
    have hbeq0 : (BitVec.ofNat 64 buffered.length == 0#64) = false := by
      rw [bv64_ofNat_beq_zero (by omega)]; exact decide_eq_false (by omega)
    have hbne_buf : (BitVec.zeroExtend 32 (buffered.getD (buffered.length - 1) 0#8) != 0x0a#32) = true :=
      zext32_bne_0a (getD_ne_of_not_mem (by omega) hbuf_noNl)
    have hbne_buf' : (BitVec.zeroExtend 32 (buffered.getD (Nat.sub buffered.length 1) 0#8) != 0x0a#32) = true :=
      hbne_buf
    rw [hbeq0]; simp only [Bool.false_eq_true, ↓reduceIte]
    wp_steps 5
    exact hbc _ _ wp_a (by simp [wp_norm, arm64_norm, hrun1]) wp_a
      (by rcases hcs1 with ⟨_, _, _, _, _, _⟩
          exact ⟨wp_a, wp_a, wp_a, wp_a, wp_a, by simp [wp_norm, arm64_norm, *]⟩)
      wp_a wp_a wp_a wp_a
      (by simp [wp_norm, arm64_norm, hfs1, hfs0]) (by simp [wp_norm, arm64_norm, htid1, htid0])
      (by simp [wp_norm, arm64_norm, htr1, htr0])
      (fun R hm => by dsimp only [hbBufWriterState]; sep_frame)

def hbAdapterWriterInv (C : HbCliLayout) (writerPtr ptrSlot g bufPtr : BitVec 64) (trace0 : List TraceEvent)
    (emitted : List (BitVec 8)) (s : State) : SepProp :=
  ∃∗ flushed : List (BitVec 8), ∃∗ buffered : List (BitVec 8),
    ⌜emitted = flushed ++ buffered ∧ buffered.length ≤ 1024 ∧ 0x0a#8 ∉ buffered ∧
      s.trace = trace0 ++ TraceEvent.ofBytes .stdout flushed⌝ ∗
    ((writerPtr ↦₆₄ ptrSlot) ∗ ((writerPtr + 8#64) ↦₆₄ 0#64) ∗ (ptrSlot ↦₆₄ g) ∗
      hbStdoutRefCell C g bufPtr buffered)

theorem hbAdapterWriterInv_nl_finish {flushed buffered pfx : List (BitVec 8)}
    (heq : pfx ++ [0x0a#8] = flushed ++ buffered) (hnoNl : 0x0a#8 ∉ buffered) :
    buffered = [] ∧ flushed = pfx ++ [0x0a#8] := by
  have hr := congrArg List.reverse heq
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append] at hr
  cases hrev : buffered.reverse with
  | nil =>
    have hb : buffered = [] := List.reverse_eq_nil_iff.mp hrev
    subst hb; exact ⟨rfl, by simpa using heq.symm⟩
  | cons x xs =>
    rw [hrev, List.cons_append] at hr
    have hx : x = 0x0a#8 := (List.cons.inj hr).1.symm
    subst hx
    exact False.elim (hnoNl (List.mem_reverse.mp (by rw [hrev]; exact .head _)))

private theorem hbAdapterWriteStr_wrap_wp {P : Program} {C : HbCliLayout}
    {writerPtr ptrSlot g bufPtr slicePtr : BitVec 64} {buffered bs : List (BitVec 8)}
    (ro : Bool) (hc : HbStdoutCode P C) {s0 : State}
    {post : State → SepProp → Prop}
    (hpc : s0.pc = C.adapterWriteStrAddr) (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = writerPtr) (hx1 : s0.readReg64 .x1 = slicePtr)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hcall : ∀ (sc : State) (F : SepProp),
      sc.pc = C.stdoutLockWriteAllAddr → sc.status = .Running →
      sc.sp = s0.sp - 48#64 → sc.spAligned = true →
      sc.readReg64 Reg.lr = C.adapterWriteStrAddr + 0x1c#64 →
      sc.readReg64 .x0 = ptrSlot → sc.readReg64 .x1 = slicePtr →
      sc.readReg64 .x2 = BitVec.ofNat 64 bs.length →
      sc.fs = s0.fs → sc.tpidrEl0 = s0.tpidrEl0 → sc.trace = s0.trace →
      (∀ (fl newBuf : List (BitVec 8)) (s1 : State),
        s1.pc = C.adapterWriteStrAddr + 0x1c#64 → s1.status = .Running →
        s1.sp = s0.sp - 48#64 → CalleeSavedPreserved sc s1 →
        s1.readReg64 .x0 = 0#64 → s1.fs = s0.fs → s1.tpidrEl0 = s0.tpidrEl0 →
        s1.trace = s0.trace ++ TraceEvent.ofBytes .stdout fl →
        (∀ sf : State,
          sf.pc = s0.readReg64 Reg.lr → sf.status = .Running →
          sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
          sf.readReg64 .x0 = 0#64 → sf.fs = s0.fs → sf.tpidrEl0 = s0.tpidrEl0 →
          sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout fl →
          post sf ((writerPtr ↦₆₄ ptrSlot) ∗ ((writerPtr + 8#64) ↦₆₄ 0#64) ∗ (ptrSlot ↦₆₄ g) ∗
            hbStdoutRefCell C g bufPtr newBuf ∗ hbBytesSlice ro slicePtr bs ∗ stackFrameAt s0.sp 304)) →
        SepWP (P.withSvc hbStdioSvc) (s0.readReg64 Reg.lr) s1
          (((ptrSlot ↦₆₄ g) ∗ hbStdoutRefCell C g bufPtr newBuf ∗ hbBytesSlice ro slicePtr bs ∗ stackAt (s0.sp - 48#64) 256) ∗ F) post) →
      SepWP (P.withSvc hbStdioSvc) (s0.readReg64 Reg.lr) sc
        (((ptrSlot ↦₆₄ g) ∗ hbStdoutRefCell C g bufPtr buffered ∗ hbBytesSlice ro slicePtr bs ∗ stackAt (s0.sp - 48#64) 256) ∗ F) post) :
    SepWP (P.withSvc hbStdioSvc) (s0.readReg64 Reg.lr) s0
      ((writerPtr ↦₆₄ ptrSlot) ∗ ((writerPtr + 8#64) ↦₆₄ 0#64) ∗ (ptrSlot ↦₆₄ g) ∗
        hbStdoutRefCell C g bufPtr buffered ∗ hbBytesSlice ro slicePtr bs ∗ stackFrameAt s0.sp 304) post := by
  have hcAd := (hc.withSvc hbStdioSvc).adapterWriteStr
  unpack_stdout_code hbAdapterWriteStrChunks hcAd
  conv => arg 4; rw [← stackAt_eq_stackFrameAt s0.sp 304, show (304 : Nat) = 48 + 256 from rfl,
    stackAt_split 48 256]
  refine SepWP.weaken_pre_frame
    (P' := stackAt s0.sp 48 ∗ (stackAt (s0.sp - 48#64) 256 ∗ (writerPtr ↦₆₄ ptrSlot) ∗
      ((writerPtr + 8#64) ↦₆₄ 0#64) ∗ (ptrSlot ↦₆₄ g) ∗
      hbStdoutRefCell C g bufPtr buffered ∗ hbBytesSlice ro slicePtr bs))
    (fun _ hm => (by sep_entail : _ → _) hm) ?_
  conv => arg 4; rw [stackAt_eq_cells s0.sp 6]
  unpack_cells 6
  wp_steps; norm_jmp
  refine SepWP.weaken_pre (P' := ((ptrSlot ↦₆₄ g) ∗ hbStdoutRefCell C g bufPtr buffered ∗
    hbBytesSlice ro slicePtr bs ∗ stackAt (s0.sp - 48#64) 256) ∗ _) (by sep_frame) ?_
  refine hcall _ _ wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
    (by simpa only [State.spAligned, wp_norm, arm64_norm] using s0.spAligned_sub 48#64 hsp_align)
    wp_a wp_a wp_a wp_a (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])
    fun fl newBuf s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hfs1 htid1 htr1 hpost => ?_
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1]; exact s0.spAligned_sub 48#64 hsp_align
  have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
  wp_steps; wp_steps
  refine SepWP.weaken_pre_frame
    (P' := (writerPtr ↦₆₄ ptrSlot) ∗ ((writerPtr + 8#64) ↦₆₄ 0#64) ∗ (ptrSlot ↦₆₄ g) ∗
      hbStdoutRefCell C g bufPtr newBuf ∗ hbBytesSlice ro slicePtr bs ∗ stackFrameAt s0.sp 304)
    (fun _ hm => by
      rw [← stackAt_eq_stackFrameAt s0.sp 304, show (304 : Nat) = 48 + 256 from rfl,
          stackAt_split 48 256, stackAt_eq_cells s0.sp 6]
      exact (by repack_cells : _ → _) hm) ?_
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1]) ?_
  exact hpost _ wp_a (by simp [wp_norm, arm64_norm, hrun1]) wp_a
    (by unpack_cs hcs1; close_cs) wp_a (by simp [wp_norm, arm64_norm, hfs1])
    (by simp [wp_norm, arm64_norm, htid1]) (by simp [wp_norm, arm64_norm, htr1])

theorem hbAdapterWriteStr_nlEnd_ro_ok {P : Program} {C : HbCliLayout}
    (writerPtr ptrSlot g bufPtr slicePtr : BitVec 64) (trace0 : List TraceEvent)
    (emitted bs : List (BitVec 8))
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C)
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hbs_lo : 1 ≤ bs.length) (hbs_hi : bs.length ≤ 15)
    (hlast : bs.getD (bs.length - 1) 0#8 = 0x0a#8)
    (hbuf_va : bufPtr.toNat + 1024 ≤ Arm64.USER_VA_LIMIT)
    (hslice_va : slicePtr.toNat + bs.length ≤ Arm64.USER_VA_LIMIT)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.adapterWriteStrAddr
      ({ pre := fun (_ : Unit) s0 =>
           ⌜s0.readReg64 .x0 = writerPtr ∧
             s0.readReg64 .x1 = slicePtr ∧
             s0.readReg64 .x2 = BitVec.ofNat 64 bs.length⌝ ∗
           hbAdapterWriterInv C writerPtr ptrSlot g bufPtr trace0 emitted s0 ∗
           (slicePtr ↦ᵣ bs) ∗
           stackFrameAt s0.sp 304
         post := fun _ s0 sf =>
           ⌜sf.readReg64 .x0 = 0#64 ∧ FmtIoStatePreserved s0 sf⌝ ∗
           hbAdapterWriterInv C writerPtr ptrSlot g bufPtr trace0 (emitted ++ bs) sf ∗
           (slicePtr ↦ᵣ bs) ∗
           stackFrameAt s0.sp 304 } : Spec Unit) := by
  apply subroutine_ok_of_sepWP_stdioSvc hext hsvc
  intro _ R s0 hpc hrun hpre hsp
  dsimp only [hbAdapterWriterInv] at hpre ⊢
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨flushed, buffered, ⟨hx0, hx1, hx2⟩, ⟨hemit, hbuf_hi, _, htr0⟩, hmem⟩
  refine ⟨(writerPtr ↦₆₄ ptrSlot) ∗ ((writerPtr + 8#64) ↦₆₄ 0#64) ∗ (ptrSlot ↦₆₄ g) ∗
    hbStdoutRefCell C g bufPtr buffered ∗ hbBytesSlice true slicePtr bs ∗ stackFrameAt s0.sp 304,
    by dsimp only [hbBytesSlice]; simpa [sepConj_assoc] using hmem, ?_⟩
  refine hbAdapterWriteStr_wrap_wp true hc hpc hrun hsp hx0 hx1 hx2
    fun sc F hpcc hrunc hspc hspc_al hlrc hx0c hx1c hx2c hfsc htidc htrc hcont => ?_
  refine hbStdoutLockWriteAll_nlEnd_stdioSvc_wp (ptrSlot := ptrSlot) (g := g) (bufPtr := bufPtr)
    (buffered := buffered) (bs := bs)
    hc hcSys hMem hMemmove hbs_lo hbs_hi hlast hbuf_hi hbuf_va hslice_va
    (fun R' hm' => by dsimp only [hbBytesSlice] at hm'; simpa [sepConj_assoc] using hm')
    (fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hfs1 htid1 htr1 => ?_)
    hpcc hrunc hspc hspc_al hlrc hx0c hx1c hx2c
  refine SepWP.weaken_pre (by dsimp only [hbBytesSlice]; exact Entails.refl _)
    (hcont (buffered ++ bs) [] s1 hpc1 hrun1 hsp1 hcs1 hx0_1 (hfsc ▸ hfs1) (htidc ▸ htid1) (htrc ▸ htr1) ?_)
  intro sf _ _ hspf hcsf hx0f hfsf htidf htrf
  refine ⟨fun hpr hmf => ?_, hspf, hcsf⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨flushed ++ (buffered ++ bs), [], ⟨hx0f, hpr.toFmtIo hfsf htidf⟩,
    ⟨by simp [hemit, List.append_assoc], by decide, by simp,
     by rw [htrf, htr0]; simp [TraceEvent.ofBytes]⟩,
    by dsimp only [hbBytesSlice] at hmf; simpa [sepConj_assoc] using hmf⟩

theorem hbAdapterFmtWriter {P : Program} {C : HbCliLayout}
    (writerPtr ptrSlot g bufPtr : BitVec 64) (trace0 : List TraceEvent)
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C)
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hbuf_va : bufPtr.toNat + 1024 ≤ Arm64.USER_VA_LIMIT)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    HbFmtWriter P C writerPtr 304 (hbAdapterWriterInv C writerPtr ptrSlot g bufPtr trace0) where
  stack_le := by decide
  pure_transport := fun emitted s1 s2 hpure => by
    dsimp only [hbAdapterWriterInv]; rw [hpure.1.2.1]; exact Entails.refl _
  write_str_owned := fun emitted bs slicePtr hbs_lo hbs_hi hbs_noNl _ _ => by
    apply subroutine_ok_of_sepWP_stdioSvc hext hsvc
    intro _ R s0 hpc hrun hpre hsp
    dsimp only [hbAdapterWriterInv] at hpre ⊢
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨flushed, buffered, ⟨hx0, hx1, hx2⟩, ⟨hemit, hbuf_hi, hbuf_noNl, htr0⟩, hmem⟩
    refine ⟨(writerPtr ↦₆₄ ptrSlot) ∗ ((writerPtr + 8#64) ↦₆₄ 0#64) ∗ (ptrSlot ↦₆₄ g) ∗
      hbStdoutRefCell C g bufPtr buffered ∗ hbBytesSlice false slicePtr bs ∗ stackFrameAt s0.sp 304,
      by dsimp only [hbBytesSlice]; simpa [sepConj_assoc] using hmem, ?_⟩
    refine hbAdapterWriteStr_wrap_wp false hc hpc hrun hsp hx0 hx1 hx2
      fun sc F hpcc hrunc hspc hspc_al hlrc hx0c hx1c hx2c hfsc htidc htrc hcont => ?_
    refine hbStdoutLockWriteAll_noNl_stdioSvc_wp (ptrSlot := ptrSlot) (g := g) (bufPtr := bufPtr)
      (buffered := buffered) (bs := bs)
      hc hcSys hMem hMemmove hbs_lo hbs_hi hbs_noNl hbuf_hi hbuf_noNl hbuf_va
      (fun R' hm' => by dsimp only [hbBytesSlice] at hm'; simpa [sepConj_assoc] using hm')
      (fun fl newBuf s1 hcat hnew_le hnew_noNl hpc1 hrun1 hsp1 hcs1 hx0_1 hfs1 htid1 htr1 => ?_)
      hpcc hrunc hspc hspc_al hlrc hx0c hx1c hx2c
    refine SepWP.weaken_pre (by dsimp only [hbBytesSlice]; exact Entails.refl _)
      (hcont fl newBuf s1 hpc1 hrun1 hsp1 hcs1 hx0_1 (hfsc ▸ hfs1) (htidc ▸ htid1) (htrc ▸ htr1) ?_)
    intro sf _ _ hspf hcsf hx0f hfsf htidf htrf
    refine ⟨fun hpr hmf => ?_, hspf, hcsf⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨flushed ++ fl, newBuf, ⟨hx0f, hpr.toFmtIo hfsf htidf⟩,
      ⟨by rw [hemit, List.append_assoc, ← hcat, ← List.append_assoc], hnew_le, hnew_noNl,
       by rw [htrf, htr0]; simp [TraceEvent.ofBytes]⟩,
      by dsimp only [hbBytesSlice] at hmf; simpa [sepConj_assoc] using hmf⟩
  write_str_ro := fun emitted bs slicePtr hbs_eq _ hsl_va => by
    subst hbs_eq
    exact hbAdapterWriteStr_nlEnd_ro_ok writerPtr ptrSlot g bufPtr slicePtr trace0 emitted [0x0a#8]
      hc hcSys hMem hMemmove (by decide) (by decide) (by decide) hbuf_va (by simp at hsl_va ⊢; omega) hsvc hext


end CaseStudies.Hashbrown.Proofs.StdCli
