/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.MainParse
public meta import ProofLib.SepLogic.Stack
public meta import ProofLib.LiteralFetchLint
import ProofLib.BV

/-!
# Newline Scanner, Print Wrappers, and Command-Loop Steps

Placement-generic `SepWP` proofs over `HbCliLayout` for the inline `0x0a` byte-scan loop,
`hashbrown_cli::print_u64` and `none` output wrappers, command-loop resource framing, and the
loop-tail and invalid-command branches of `hashbrown_cli::main`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown CaseStudies.Hashbrown.Proofs

local macro "unpack_loop_code " h:term : tactic => `(tactic| (
  have _hc := stdoutToStepFacts $h
  simp only [hbRustMainLoopChunks, stdoutStepFacts, stdoutStepAcc, fetchAtAcc',
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

local macro "unpack_stdout_code " chunks:ident h:term : tactic => `(tactic| (
  have _hc := stdoutToStepFacts $h
  simp only [$chunks:ident, stdoutStepFacts, stdoutStepAcc, fetchAtAcc',
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

local macro "norm_jmp" : tactic =>
  `(tactic| conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel])
local macro "close_cs" : tactic =>
  `(tactic| simp [CalleeSavedPreserved.iff_regs, Reg.fp, wp_norm, arm64_norm, *])
local macro "close_cpu_step " s:term : term =>
  `(⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [CpuAuxPreserved.refl $s], by close_cs⟩)
local macro "wp_a" : term => `(by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)

attribute [local simp] cpuAux_writeReg64 cpuAux_writeReg32 cpuAux_writeReg
  cpuAux_setPState cpuAux_advancePC cpuAux_setPC cpuAux_setMem

/-! ## Newline Scanner (`u + 0x184 .. u + 0x1d4`) -/

/-- State preservation across the inline `0x0a` byte-scan loop at `u + 0x184 .. u + 0x1d4`
    (modifies `x1`, `x8`, `x9`, `x22`, `x26`, `x27`, `pstate`, `pc`; preserves `sp`, `fs`, `trace`,
    `CpuAuxPreserved`, `calleeSavedVRegs`, and `x19, x20, x21, x23, x24, x25, x28, x29`). -/
def NlScanPreserved (s0 sf : State) : Prop :=
  sf.sp = s0.sp ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
  CpuAuxPreserved s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
  sf.readReg64 .x19 = s0.readReg64 .x19 ∧ sf.readReg64 .x20 = s0.readReg64 .x20 ∧
  sf.readReg64 .x21 = s0.readReg64 .x21 ∧ sf.readReg64 .x23 = s0.readReg64 .x23 ∧
  sf.readReg64 .x24 = s0.readReg64 .x24 ∧ sf.readReg64 .x25 = s0.readReg64 .x25 ∧
  sf.readReg64 .x28 = s0.readReg64 .x28 ∧ sf.readReg64 .x29 = s0.readReg64 .x29

theorem NlScanPreserved.trans {s0 s1 s2 : State}
    (h01 : NlScanPreserved s0 s1) (h12 : NlScanPreserved s1 s2) : NlScanPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h01.2.2.2.1.trans h12.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2.2.2.2.2.2⟩

local macro "close_nl_step " s:term : term =>
  `(⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [CpuAuxPreserved.refl $s],
     by simp [calleeSavedVRegs, wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩)

theorem HbMainCmdCode.nlScan {P : Program} {C : HbCliLayout} (h : HbMainCmdCode P C) :
    P.hasCode (C.std.userMainAddr + 0x184#64) hbNlScanWords :=
  h.rustMainLoop.2.2.2.2.2.2.2.2.2.2.2.1

private theorem nlScan_loop_wp {Q : Program} {u target remPtr : BitVec 64}
    {rem : List (BitVec 8)} {fuel idx : Nat} {s0 : State} {F : SepProp}
    {post : State → SepProp → Prop}
    (hcNl : Q.hasCode (u + 0x184#64) hbNlScanWords)
    (hfuel : rem.length - idx ≤ fuel) (hidx : idx < rem.length)
    (hptr_nz : remPtr ≠ 0#64) (hptr_fit : remPtr.toNat + rem.length < 2 ^ 64)
    (hprev : ∀ j (hj : j < idx), rem[j]'(by omega) ≠ 0x0a#8)
    (hpc : s0.pc = u + 0x18c#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = remPtr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 idx)
    (hx22 : s0.readReg64 .x22 = BitVec.ofNat 64 rem.length)
    (hMore : ∀ (sf : State) (k : Nat),
      let curLine := rem.take k
      let restBytes := rem.drop (k + 1)
      let nextPtr := remPtr + BitVec.ofNat 64 (k + 1)
      k < rem.length →
      splitOnByte 0x0a#8 rem = curLine :: splitOnByte 0x0a#8 restBytes →
      remPtr.toNat + curLine.length < 2 ^ 64 →
      nextPtr ≠ 0#64 → nextPtr.toNat + restBytes.length < 2 ^ 64 →
      sf.pc = u + 0x1d4#64 → sf.status = .Running → NlScanPreserved s0 sf →
      sf.readReg64 .x0 = remPtr →
      sf.readReg64 .x1 = BitVec.ofNat 64 curLine.length →
      sf.readReg64 .x26 = 0#64 →
      sf.readReg64 .x27 = nextPtr →
      sf.readReg64 .x22 = BitVec.ofNat 64 restBytes.length →
      SepWP Q target sf
        ((remPtr ↦ₛ curLine) ∗ ((remPtr + BitVec.ofNat 64 k) ↦₈ 0x0a#8) ∗
         (nextPtr ↦ₛ restBytes) ∗ F) post)
    (hLast : ∀ sf : State,
      splitOnByte 0x0a#8 rem = [rem] →
      sf.pc = u + 0x1d4#64 → sf.status = .Running → NlScanPreserved s0 sf →
      sf.readReg64 .x0 = remPtr →
      sf.readReg64 .x1 = BitVec.ofNat 64 rem.length →
      sf.readReg64 .x26 = 1#64 →
      sf.readReg64 .x27 = remPtr →
      SepWP Q target sf ((remPtr ↦ₛ rem) ∗ F) post) :
    SepWP Q target s0 ((remPtr ↦ₛ rem) ∗ F) post := by
  have hlen : rem.length < 2 ^ 64 := by omega
  induction fuel generalizing idx s0 with
  | zero => omega
  | succ fuel ih =>
    have hb_eq : rem.getD idx 0#8 = rem[idx] := by simp [List.getD, hidx]
    conv => arg 4; rw [pointsToBytes_focus8 remPtr rem idx hidx]
    wp_steps 2
    have hcond : (rem[idx].zeroExtend 32 == 0x0a#32) = (rem[idx] == 0x0a#8) :=
      ze32_beq_byte rem[idx] 0x0a#8
    by_cases hnl : rem[idx] = 0x0a#8
    · have hbeq : (rem[idx].zeroExtend 32 == 0x0a#32) = true := by
        rw [hcond]; exact beq_iff_eq.mpr hnl
      have hmvn : ~~~(BitVec.ofNat 64 idx) + BitVec.ofNat 64 rem.length =
          BitVec.ofNat 64 (rem.drop (idx + 1)).length := by
        rw [mvn_add_of_lt hidx hlen, List.length_drop]
      have hadd1 : remPtr + BitVec.ofNat 64 idx + 1#64 = remPtr + BitVec.ofNat 64 (idx + 1) := by
        rw [BitVec.ofNat_add]; bv_lin
      have hcur_len : (rem.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
      have hptr_pos : 0 < remPtr.toNat := Nat.pos_of_ne_zero fun h => hptr_nz (BitVec.eq_of_toNat_eq h)
      have hnext_toNat : (remPtr + BitVec.ofNat 64 (idx + 1)).toNat = remPtr.toNat + (idx + 1) := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
      have hnext_nz : remPtr + BitVec.ofNat 64 (idx + 1) ≠ 0#64 := fun h => by
        have ht := congrArg BitVec.toNat h; simp [hnext_toNat] at ht
      have hnext_fit : (remPtr + BitVec.ofNat 64 (idx + 1)).toNat + (rem.drop (idx + 1)).length < 2 ^ 64 := by
        rw [hnext_toNat, List.length_drop]; omega
      wp_steps 6
      rw [hb_eq, hnl]
      exact SepWP.weaken_pre (by sep_frame)
        (hMore _ idx hidx (splitOnByte_of_first_eq hidx hnl hprev)
          (by rw [hcur_len]; omega) hnext_nz hnext_fit
          wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_nl_step s0)
          wp_a (by rw [hcur_len]; exact wp_a) wp_a wp_a wp_a)
    · have hbeq : (rem[idx].zeroExtend 32 == 0x0a#32) = false := by
        rw [hcond]; exact beq_eq_false_iff_ne.mpr hnl
      have hidx1 : BitVec.ofNat 64 idx + 1#64 = BitVec.ofNat 64 (idx + 1) :=
        (BitVec.ofNat_add idx 1).symm
      wp_steps 3
      by_cases hmore : idx + 1 < rem.length
      · have hbne : (BitVec.ofNat 64 rem.length != BitVec.ofNat 64 (idx + 1)) = true := by
          rw [bne_iff_ne]; intro he; have ht := congrArg BitVec.toNat he
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt (by omega)] at ht
          omega
        wp_steps 1
        conv => arg 4; rw [← pointsToBytes_focus8 remPtr rem idx hidx]
        have hprev' : ∀ j (hj : j < idx + 1), rem[j]'(by omega) ≠ 0x0a#8 := fun j hj => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
          · exact hprev j hlt
          · exact hnl
        exact ih (idx := idx + 1) (by omega) hmore hprev'
          wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a wp_a wp_a
          (fun sf k hk h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
            hMore sf k hk h1 h2 h3 h4 h5 h6 (NlScanPreserved.trans (close_nl_step s0) h7) h8 h9 h10 h11 h12)
          (fun sf h1 h2 h3 h4 h5 h6 h7 h8 =>
            hLast sf h1 h2 h3 (NlScanPreserved.trans (close_nl_step s0) h4) h5 h6 h7 h8)
      · have heq_len : idx + 1 = rem.length := by omega
        have hbne : (BitVec.ofNat 64 rem.length != BitVec.ofNat 64 (idx + 1)) = false := by
          rw [heq_len]; simp
        have hall : ∀ j (hj : j < rem.length), rem[j] ≠ 0x0a#8 := fun j hj => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp (heq_len ▸ hj) with hlt | rfl
          · exact hprev j hlt
          · exact hnl
        wp_steps 5
        conv => arg 4; rw [← pointsToBytes_focus8 remPtr rem idx hidx]
        exact hLast _ (splitOnByte_of_forall_ne (List.ne_nil_of_length_pos (by omega)) hall)
          wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_nl_step s0) wp_a wp_a wp_a wp_a

theorem nlScan_wp {Q : Program} {C : HbCliLayout} {target remPtr : BitVec 64}
    {rem : List (BitVec 8)} {s0 : State} {F : SepProp} {post : State → SepProp → Prop}
    (hc : HbMainCmdCode Q C)
    (hptr_nz : remPtr ≠ 0#64) (hptr_fit : remPtr.toNat + rem.length < 2 ^ 64)
    (hpc : s0.pc = C.std.userMainAddr + 0x184#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = remPtr)
    (hx22 : s0.readReg64 .x22 = BitVec.ofNat 64 rem.length)
    (hMore : ∀ (sf : State) (k : Nat),
      let curLine := rem.take k
      let restBytes := rem.drop (k + 1)
      let nextPtr := remPtr + BitVec.ofNat 64 (k + 1)
      k < rem.length →
      splitOnByte 0x0a#8 rem = curLine :: splitOnByte 0x0a#8 restBytes →
      remPtr.toNat + curLine.length < 2 ^ 64 →
      nextPtr ≠ 0#64 → nextPtr.toNat + restBytes.length < 2 ^ 64 →
      sf.pc = C.std.userMainAddr + 0x1d4#64 → sf.status = .Running → NlScanPreserved s0 sf →
      sf.readReg64 .x0 = remPtr →
      sf.readReg64 .x1 = BitVec.ofNat 64 curLine.length →
      sf.readReg64 .x26 = 0#64 →
      sf.readReg64 .x27 = nextPtr →
      sf.readReg64 .x22 = BitVec.ofNat 64 restBytes.length →
      SepWP Q target sf
        ((remPtr ↦ₛ curLine) ∗ ((remPtr + BitVec.ofNat 64 k) ↦₈ 0x0a#8) ∗
         (nextPtr ↦ₛ restBytes) ∗ F) post)
    (hLast : ∀ sf : State,
      splitOnByte 0x0a#8 rem = [rem] →
      sf.pc = C.std.userMainAddr + 0x1d4#64 → sf.status = .Running → NlScanPreserved s0 sf →
      sf.readReg64 .x0 = remPtr →
      sf.readReg64 .x1 = BitVec.ofNat 64 rem.length →
      sf.readReg64 .x26 = 1#64 →
      sf.readReg64 .x27 = remPtr →
      SepWP Q target sf ((remPtr ↦ₛ rem) ∗ F) post) :
    SepWP Q target s0 ((remPtr ↦ₛ rem) ∗ F) post := by
  have hcNl := hc.nlScan
  rcases rem with _ | ⟨b, rest⟩
  · wp_steps 5
    exact hLast _ (splitOnByte_nil 0x0a#8) wp_a (by simp [wp_norm, arm64_norm, hrun])
      (close_nl_step s0) wp_a wp_a wp_a wp_a
  · have hlen : (b :: rest).length < 2 ^ 64 := by omega
    have hnz : (BitVec.ofNat 64 (b :: rest).length == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro he; have ht := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen] at ht; simp at ht
    wp_steps 2
    exact nlScan_loop_wp hcNl (fuel := (b :: rest).length) (idx := 0) (by omega)
      (by simp) hptr_nz hptr_fit (fun _ hj => by omega)
      wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a wp_a wp_a
      (fun sf k hk h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
        hMore sf k hk h1 h2 h3 h4 h5 h6 (NlScanPreserved.trans (close_nl_step s0) h7) h8 h9 h10 h11 h12)
      (fun sf h1 h2 h3 h4 h5 h6 h7 h8 =>
        hLast sf h1 h2 h3 (NlScanPreserved.trans (close_nl_step s0) h4) h5 h6 h7 h8)

/-! ## `hashbrown_cli::print_u64` and `none` Print -/

private theorem align16_and_one_zero {a : BitVec 64} (h : (a &&& 15#64 == 0#64) = true) :
    a &&& 1#64 = 0#64 := by
  have h0 := beq_iff_eq.mp h; bv_bits

private theorem sp_sub48_lo {sp0 : BitVec 64} (h : 0x310 ≤ sp0.toNat) :
    0x2e0 ≤ (sp0 - 48#64).toNat := by
  have h48 : (48#64 : BitVec 64).toNat = 48 := rfl
  rw [BitVec.toNat_sub_of_le (by omega : (48#64 : BitVec 64).toNat ≤ sp0.toNat), h48]; omega

theorem hbPrintU64_tidInv_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) (v : BitVec 64) (init : Bool)
    {target_pc ret_pc sp0 : BitVec 64}
    {lc blk : Nat} {e0 : BitVec 32} {haveLse : BitVec 8}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C)
    (honce : HbOnceCallCode P C)
    (hcas8 : subroutine_ok P C.std.cas8RelaxAddr (stdCas8Spec C.std.haveLseAtomicsAddr))
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64)
    (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hsp_lo : 0x310 ≤ sp0.toNat)
    (hbudget : init = false → 1024 ≤ lim.maxReq ∧
      lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks)
    (hpc : s0.pc = C.printU64Addr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_al : s0.spAligned = true) (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hx0 : s0.readReg64 .x0 = v)
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs → sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout (formatGetResult (some v)) →
      sf.sigActions = s0.sigActions → sf.tpidrEl0 = s0.tpidrEl0 →
      SepWP P target_pc sf
        ((HbStdoutInv C M γ true ∗ HbAdapterWriteVtableRo C ∗
          (C.nlByteAddr ↦ᵣ nlByteBytes) ∗ (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
          (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
          StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
          (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C sf.tpidrEl0 ∗
          M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt sp0 4432) ∗ F) post oom) :
    SepWP P target_pc s0
      ((HbStdoutInv C M γ init ∗ HbAdapterWriteVtableRo C ∗
        (C.nlByteAddr ↦ᵣ nlByteBytes) ∗ (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
        (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C s0.tpidrEl0 ∗
        M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt sp0 4432) ∗ F) post oom := by
  subst hsp
  have hlr' : s0.readReg64 (.gpr 30#5) = ret_pc := hlr
  have hx0' : s0.readReg64 (.gpr 0#5) = v := hx0
  have hsp1_al : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := s0.spAligned_sub 48#64 hsp_al
  have harg1_al : (s0.sp - 32#64) &&& 1#64 = 0#64 := align16_and_one_zero (s0.spAligned_sub 32#64 hsp_al)
  have hnl_fit : C.nlByteAddr.toNat + 12 ≤ Arm64.USER_VA_LIMIT := hv.nlByte_noWrap
  have hnl_eq : nlByteBytes = fmtValNlTemplateBytes := rfl
  have h32_8 : (s0.sp - 32#64) + 8#64 = s0.sp - 24#64 := by bv_lin
  conv => arg 4; rw [show (4432 : Nat) = 4384 + 8 * 6 from rfl,
    stackAt_split_cells s0.sp 4384 6 (by decide)]
  simp only [Nat.reduceMul]
  cells_unfold
  try simp only [sepExists_sepConj_right]
  try simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro w0
  iterate 5 (apply SepWP.exists_left; intro _)
  conv => arg 4; simp only [sepConj_assoc]
  refine sepWP_cpu_seg (mid_pc := C.stdioPrintAddr) hext ?_
  have hchunk := (hc.withSvc noSyscalls).printU64
  unpack_stdout_code hbPrintU64Chunks hchunk
  wp_steps 5; wp_steps 1; wp_steps 2; wp_steps 1; wp_steps 2; wp_steps 1
  conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel']
  conv => repeat rw [bv64_add_sub_cancel']
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
    ⟨by simp [CpuAuxPreserved.refl s0], fun hpure1 => ?_⟩
  refine SepWP.weaken_pre
    (P' := (HbStdoutInv C M γ init ∗
      hbStdioPrintInputRes C (some v) C.nlByteAddr (s0.sp - 32#64) (s0.sp - 40#64) ∗
      (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
      (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C _ ∗
      M.Heap γ lc blk _ ∗ (muslErrnoAddr _ ↦₃₂ e0) ∗ stackAt (s0.sp - 48#64) 4384) ∗
      (((s0.sp - 48#64) ↦₆₄ _) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
       ((s0.sp - 8#64) ↦₆₄ ret_pc) ∗ F))
    (by
      dsimp only [hbStdioPrintInputRes, hbCoreFmtWriteU64NlRes, muslErrnoAddr]
      rw [heap_eq_of_std M hpure1.1, ← hpure1.1.2.2.1, h32_8, ← hnl_eq,
          pure_sepConj_of_true ⟨hv.nlByte_nz, hnl_fit, harg1_al⟩]
      sep_entail)
    (hbStdioPrint_getResult_tidInv_wp M γ (some v) init (ret_pc := C.printU64Addr + 0x30#64)
      hc hcSys hfmt honce hcas8 hcas4 hswp4 hMem hMemmove hv hg_nz hsvc hext
      (fun _ => sp_sub48_lo hsp_lo) hbudget
      wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
      (by simp only [State.spAligned, wp_norm, arm64_norm]
          simpa [BitVec.sub_eq_add_neg] using hsp1_al)
      wp_a wp_a wp_a
      fun s2 e1 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 hsig2 htp2 => ?_)
  have hsp2_eq : s2.sp = s0.sp - 48#64 := hsp2.trans wp_a
  refine sepWP_cpu_seg (mid_pc := ret_pc) hext ?_
  have hchunk2 := (hc.withSvc noSyscalls).printU64
  unpack_stdout_code hbPrintU64Chunks hchunk2
  dsimp only [hbStdioPrintInputRes, hbCoreFmtWriteU64NlRes]
  rw [h32_8, ← hnl_eq]
  conv => arg 4; simp only [sepConj_assoc]; rw [sepConj_left_comm (HbStdoutInv C M γ true)]
  apply SepWP.pure_elim; intro _
  have hoff20 : s2.sp + 32#64 = s0.sp - 16#64 := by rw [hsp2_eq]; bv_lin
  have hoff28 : (s0.sp - 16#64) + 8#64 = s0.sp - 8#64 := by bv_lin
  have hadd30 : s2.sp + 48#64 = s0.sp := by rw [hsp2_eq]; bv_lin
  wp_steps 3
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun2])
    ⟨by simp [CpuAuxPreserved.refl s2], fun hpure3 => ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := hcs2
  refine SepWP.weaken_pre_frame (fun R hm => ?_)
    (hnext _ e1 wp_a (by simp [wp_norm, arm64_norm, hrun2])
      wp_a (by close_cs)
      (hpure3.1.1.trans (hfs2.trans hpure1.1.1))
      (by rw [hpure3.1.2.1, htr2, hpure1.1.2.1])
      (hpure3.1.2.2.2.1.trans (hsig2.trans hpure1.1.2.2.2.1))
      (hpure3.1.2.2.1.trans (htp2.trans hpure1.1.2.2.1)))
  rw [heap_eq_of_std M hpure3.1] at hm
  dsimp only [muslErrnoAddr] at hm ⊢
  rw [← hpure3.1.2.2.1] at hm
  rw [show (4432 : Nat) = 4384 + 8 * 6 from rfl, stackAt_split_cells s0.sp 4384 6 (by decide)]
  try simp only [Nat.reduceMul] at hm ⊢
  try simp only [wp_norm, arm64_norm] at hm ⊢
  have hcells : ((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ v) ∗
      ((s0.sp - 32#64) ↦₆₄ (s0.sp - 40#64)) ∗ ((s0.sp - 24#64) ↦₆₄ C.u64DisplayFmtAddr) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((s0.sp - 8#64) ↦₆₄ ret_pc) ⊢
      cells (s0.sp - 48#64) 6 := by
    cells_unfold
    exact Entails.sepExists_right w0 (Entails.sepExists_right v
      (Entails.sepExists_right (s0.sp - 40#64) (Entails.sepExists_right C.u64DisplayFmtAddr
        (Entails.sepExists_right (s0.readReg64 (.gpr 29#5))
          (Entails.sepExists_right ret_pc (by sep_entail))))))
  exact Satisfies.mono (Entails.trans (by sep_frame) (Entails.trans (sepConj_mono_left hcells) (by sep_entail))) hm

def hbPrintU64Spec {P : Program} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) :
    Spec (BitVec 64 × Bool × Nat × Nat × BitVec 32 × BitVec 8) where
  pre := fun (v, init, lc, blk, e0, haveLse) s0 =>
    ⌜s0.readReg64 .x0 = v ∧ 0x310 ≤ s0.sp.toNat ∧
      (init = false → 1024 ≤ lim.maxReq ∧
        lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks)⌝ ∗
    HbStdoutInv C M γ init ∗ HbAdapterWriteVtableRo C ∗
    (C.nlByteAddr ↦ᵣ nlByteBytes) ∗ (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
    (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C s0.tpidrEl0 ∗
    M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt s0.sp 4432
  post := fun (v, init, lc, blk, _, haveLse) s0 sf =>
    ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout (formatGetResult (some v)) ∧
      sf.sigActions = s0.sigActions ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗
    HbStdoutInv C M γ true ∗ HbAdapterWriteVtableRo C ∗
    (C.nlByteAddr ↦ᵣ nlByteBytes) ∗ (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
    (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C sf.tpidrEl0 ∗
    M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) sf ∗
    (∃∗ e1 : BitVec 32, muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt s0.sp 4432

theorem hbPrintU64_ok {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C)
    (honce : HbOnceCallCode P C)
    (hcas8 : subroutine_ok P C.std.cas8RelaxAddr (stdCas8Spec C.std.haveLseAtomicsAddr))
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64) (hsvc : P.svc = Syscall.standard)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.printU64Addr (hbPrintU64Spec C M γ) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨v, init, lc, blk, e0, haveLse⟩ R s0 hpc hrun hpre hsp
  dsimp only [hbPrintU64Spec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hsp_lo, hbudget⟩, hmem⟩
  refine ⟨(HbStdoutInv C M γ init ∗ HbAdapterWriteVtableRo C ∗
    (C.nlByteAddr ↦ᵣ nlByteBytes) ∗ (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
    (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C s0.tpidrEl0 ∗
    M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt s0.sp 4432) ∗ emp,
    by simpa [sepConj_emp, sepConj_assoc] using hmem, ?_⟩
  refine hbPrintU64_tidInv_wp M γ v init hc hcSys hfmt honce hcas8 hcas4 hswp4
    hMem hMemmove hv hg_nz hsvc hext hsp_lo hbudget hpc hrun rfl hsp rfl hx0
    fun sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf => ?_
  refine SepWP.done hpcf hrunf ⟨fun hm => ?_, hspf, hcsf⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hfsf, htrf, hsigf, htpf⟩, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_emp, sepConj_assoc] at hm ⊢
  exact Satisfies.mono (Entails.sepExists_right e1 (by sep_entail)) hm

def hbStdioPrintNoneSpec {P : Program} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) :
    Spec (Bool × Nat × Nat × BitVec 32 × BitVec 8) where
  pre := fun (init, lc, blk, e0, haveLse) s0 =>
    ⌜s0.readReg64 .x0 = C.noneNlAddr ∧ s0.readReg64 .x1 = 0x0b#64 ∧
      (init = false → 1024 ≤ lim.maxReq ∧
        lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks)⌝ ∗
    HbStdoutInv C M γ init ∗ HbAdapterWriteVtableRo C ∗
    (C.noneNlAddr ↦ᵣ noneNlBytes) ∗
    (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C s0.tpidrEl0 ∗
    M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt s0.sp 4384
  post := fun (init, lc, blk, _, haveLse) s0 sf =>
    ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout (formatGetResult none) ∧
      sf.sigActions = s0.sigActions ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗
    HbStdoutInv C M γ true ∗ HbAdapterWriteVtableRo C ∗
    (C.noneNlAddr ↦ᵣ noneNlBytes) ∗
    (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C sf.tpidrEl0 ∗
    M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) sf ∗
    (∃∗ e1 : BitVec 32, muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt s0.sp 4384

theorem hbStdioPrintNone_ok {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C)
    (honce : HbOnceCallCode P C)
    (hcas8 : subroutine_ok P C.std.cas8RelaxAddr (stdCas8Spec C.std.haveLseAtomicsAddr))
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64) (hsvc : P.svc = Syscall.standard)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.stdioPrintAddr (hbStdioPrintNoneSpec C M γ) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨init, lc, blk, e0, haveLse⟩ R s0 hpc hrun hpre hsp
  dsimp only [hbStdioPrintNoneSpec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hbudget⟩, hmem⟩
  refine ⟨(HbStdoutInv C M γ init ∗ hbStdioPrintInputRes C none C.noneNlAddr 0x0b#64 0#64 ∗
    (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ HbThreadIdInv C s0.tpidrEl0 ∗
    M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt s0.sp 4384) ∗ emp,
    by dsimp only [hbStdioPrintInputRes]; rw [pure_sepConj_of_true ⟨rfl, rfl⟩]
       exact Satisfies.mono (by sep_entail) hmem, ?_⟩
  refine hbStdioPrint_getResult_tidInv_wp M γ none init hc hcSys hfmt honce hcas8 hcas4 hswp4
    hMem hMemmove hv hg_nz hsvc hext (by intro h; cases h) hbudget hpc hrun rfl hsp rfl hx0 hx1
    fun sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf => ?_
  refine SepWP.done hpcf hrunf ⟨fun hm => ?_, hspf, hcsf⟩
  dsimp only [hbStdioPrintInputRes] at hm
  rw [pure_sepConj_of_true ⟨rfl, rfl⟩] at hm
  simp only [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hfsf, htrf, hsigf, htpf⟩, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_emp, sepConj_assoc] at hm ⊢
  exact Satisfies.mono (Entails.sepExists_right e1 (by sep_entail)) hm

/-! ## Command-Loop Resource Bundles, Frame Splits, and Callee Bundle -/

def HbCmdRoData (C : HbCliLayout) : SepProp :=
  HbParseRoData C ∗
  (C.falseNlAddr ↦ᵣ falseNlBytes) ∗ (C.trueNlAddr ↦ᵣ trueNlBytes) ∗
  (C.errInvalidCmdAddr ↦ᵣ errInvalidCmdBytes) ∗ (C.noneNlAddr ↦ᵣ noneNlBytes) ∗
  (C.nlByteAddr ↦ᵣ nlByteBytes) ∗ (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
  StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
  HbAdapterWriteVtableRo C ∗
  (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
  (C.captureUsedAddr ↦₈ᵣ 0#8)

theorem hbCliRoData_eq_cmdRoData (C : HbCliLayout) :
    HbCliRoData C =
      HbCmdRoData C ∗
      (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗
      StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
      (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) := by
  apply Entails.antisymm <;> (unfold HbCliRoData HbCmdRoData HbParseRoData; sep_entail)

/-- Machine-state invariant across iterations of `hashbrown_cli::main`'s command loop
    (`u + 0x170 .. u + 0x300`). Note `x21` is omitted because the `withCapacity` arm overwrites
    `x21` with `cap` at `u + 0x2cc`. -/
def CmdLoopState (C : HbCliLayout) (sp_m : BitVec 64) (s_ref s : State) : Prop :=
  s.sp = sp_m ∧ s.spAligned = true ∧ s.fs = s_ref.fs ∧ s.tpidrEl0 = s_ref.tpidrEl0 ∧
  s.sigActions = s_ref.sigActions ∧ calleeSavedVRegs s = calleeSavedVRegs s_ref ∧
  s.readReg64 .x19 = C.errInvalidCmdAddr ∧ s.readReg64 .x20 = C.noneNlAddr ∧
  s.readReg64 .x23 = C.stderrGlobalAddr ∧ s.readReg64 .x24 = sp_m + 0x60#64 ∧
  s.readReg64 .x25 = 3#64 ∧ s.readReg64 .x28 = s_ref.readReg64 .x28 ∧
  s.readReg64 .x29 = sp_m + 0x80#64

theorem CmdLoopState.of_cs_fs {C : HbCliLayout} {sp_m : BitVec 64} {s_ref s sf : State}
    (hs : CmdLoopState C sp_m s_ref s) (hsp : sf.sp = s.sp) (hfs : sf.fs = s.fs)
    (htp : sf.tpidrEl0 = s.tpidrEl0) (hsig : sf.sigActions = s.sigActions)
    (hcs : CalleeSavedPreserved s sf) : CmdLoopState C sp_m s_ref sf := by
  rcases hs with ⟨h0, hal, hf0, ht0, hsg0, hv0, r19, r20, r23, r24, r25, r28, r29⟩
  exact ⟨hsp.trans h0, by simpa [State.spAligned, hsp] using hal, hfs.trans hf0, htp.trans ht0,
    hsig.trans hsg0, hcs.vregs.trans hv0, hcs.readReg64_x19.trans r19,
    hcs.readReg64_x20.trans r20, hcs.readReg64_x23.trans r23, hcs.readReg64_x24.trans r24,
    hcs.readReg64_x25.trans r25, hcs.readReg64_x28.trans r28, hcs.readReg64_x29.trans r29⟩

theorem CmdLoopState.of_cpu {C : HbCliLayout} {sp_m : BitVec 64} {s_ref s sf : State}
    (hs : CmdLoopState C sp_m s_ref s) (hcpu : PureCpuStep s sf) :
    CmdLoopState C sp_m s_ref sf :=
  hs.of_cs_fs hcpu.1 hcpu.2.1 hcpu.2.2.2.1.1 hcpu.2.2.2.1.2.1 hcpu.2.2.2.2

theorem CmdLoopState.of_nlScan {C : HbCliLayout} {sp_m : BitVec 64} {s_ref s sf : State}
    (hs : CmdLoopState C sp_m s_ref s) (hnl : NlScanPreserved s sf) :
    CmdLoopState C sp_m s_ref sf := by
  rcases hs with ⟨h0, hal, hf0, ht0, hsg0, hv0, r19, r20, r23, r24, r25, r28, r29⟩
  rcases hnl with ⟨hsp, hfs, _, haux, hv, s19, s20, _, s23, s24, s25, s28, s29⟩
  exact ⟨hsp.trans h0, by simpa [State.spAligned, hsp] using hal, hfs.trans hf0, haux.1.trans ht0,
    haux.2.1.trans hsg0, hv.trans hv0, s19.trans r19, s20.trans r20, s23.trans r23,
    s24.trans r24, s25.trans r25, s28.trans r28, s29.trans r29⟩

def CmdLoopRest {P : Program} {L : Nat} (C : HbCliLayout)
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (sp_m : BitVec 64) (haveLse : BitVec 8) (baseLc baseBlk : Nat)
    (bm : BitVec 64) (init : Bool) (e_err : BitVec 32) (c0 c1 c2 : BitVec 64) (s : State) : SepProp :=
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  M.Heap γ (baseLc + hbStdoutCost init + hbMapCost A bm) (baseBlk + hbStdoutBlocks init + tableAllocBlocks bm) s ∗
  HbStdoutInv C M γ init ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbCmdRoData C ∗
  (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ HbThreadIdInv C s.tpidrEl0 ∗ (muslErrnoAddr s ↦₃₂ e_err) ∗
  memRegion (sp_m + 0x40#64) 8 ∗
  ((sp_m + 0x48#64) ↦₆₄ c0) ∗ ((sp_m + 0x50#64) ↦₆₄ c1) ∗ ((sp_m + 0x58#64) ↦₆₄ c2) ∗
  memRegion (sp_m + 0x60#64) 32 ∗ memRegion (sp_m + 0x98#64) 8 ∗ stackAt sp_m 4432

def CmdLoopRes {P : Program} {L : Nat} (C : HbCliLayout)
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (sp_m : BitVec 64) (haveLse : BitVec 8) (baseLc baseBlk : Nat)
    (m : Map64) (bm : BitVec 64) (u : Nat) (init : Bool) (e_err : BitVec 32) (c0 c1 c2 : BitVec 64) (s : State) : SepProp :=
  U64MapRep C.hbPl (HbAlloc.ofMallocng M γ CodeInv hCodeInv) (sp_m + 0x20#64) m bm u ∗
  CmdLoopRest C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0 c1 c2 s

theorem CmdLoopRest.transport {P : Program} {L : Nat} {C : HbCliLayout}
    {M : MallocngCoreIface P C.mallocng (hbStdLimits L)} {γ : GhostName} {CodeInv : Memory → Prop}
    {hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2}
    {sp_m : BitVec 64} {haveLse : BitVec 8} {baseLc baseBlk : Nat}
    {bm : BitVec 64} {init : Bool} {e_err : BitVec 32} {c0 c1 c2 : BitVec 64} {s sf : State}
    (htp : sf.tpidrEl0 = s.tpidrEl0)
    (hht : M.Heap γ (baseLc + hbStdoutCost init + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm)
                    (baseBlk + hbStdoutBlocks init + tableAllocBlocks bm) s ⊢
           M.Heap γ (baseLc + hbStdoutCost init + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm)
                    (baseBlk + hbStdoutBlocks init + tableAllocBlocks bm) sf) :
    CmdLoopRest C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0 c1 c2 s ⊢
    CmdLoopRest C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk bm init e_err c0 c1 c2 sf := by
  unfold CmdLoopRest
  have herr : muslErrnoAddr s = muslErrnoAddr sf := by simp [muslErrnoAddr, htp]
  rw [herr, ← htp]; exact sepConj_mono_left hht

theorem CmdLoopRes.transport {P : Program} {L : Nat} {C : HbCliLayout}
    {M : MallocngCoreIface P C.mallocng (hbStdLimits L)} {γ : GhostName} {CodeInv : Memory → Prop}
    {hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2}
    {sp_m : BitVec 64} {haveLse : BitVec 8} {baseLc baseBlk : Nat}
    {m : Map64} {bm : BitVec 64} {u : Nat} {init : Bool} {e_err : BitVec 32} {c0 c1 c2 : BitVec 64} {s sf : State}
    (htp : sf.tpidrEl0 = s.tpidrEl0) (hvm : VmFieldsPreserved s sf) :
    CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 s ⊢
    CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 sf :=
  sepConj_mono_right (CmdLoopRest.transport htp
    (M.heap_transport hvm.brk_eq hvm.brkStart_eq hvm.physMemAvail_eq hvm.perm_eq))

theorem CmdLoopRes.mono_u {P : Program} {L : Nat} {C : HbCliLayout}
    {M : MallocngCoreIface P C.mallocng (hbStdLimits L)} {γ : GhostName} {CodeInv : Memory → Prop}
    {hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2}
    {sp_m : BitVec 64} {haveLse : BitVec 8} {baseLc baseBlk : Nat}
    {m : Map64} {bm : BitVec 64} {u u' : Nat} {init : Bool} {e_err : BitVec 32} {c0 c1 c2 : BitVec 64} {s : State}
    (hu : u ≤ u') :
    CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 s ⊢
    CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u' init e_err c0 c1 c2 s :=
  sepConj_mono_left (U64MapRep_mono_u _ _ _ _ _ hu)

theorem sp_main_frame_facts {s0 : State} {sp_m : BitVec 64}
    (hsp_al : s0.spAligned = true) (hsp : s0.sp = sp_m) (hsp_hi : sp_m.toNat + 0x80 ≤ 2 ^ 64) :
    (sp_m + 0x20#64).toNat % 8 = 0 ∧ (sp_m + 0x20#64).toNat + 32 ≤ 2 ^ 64 ∧
    (sp_m + 0x60#64).toNat % 8 = 0 ∧ (sp_m + 0x60#64).toNat + 32 ≤ 2 ^ 64 := by
  have hal16 : sp_m.toNat % 16 = 0 := by
    simp only [State.spAligned, hsp, beq_iff_eq] at hsp_al
    have ht : sp_m.toNat &&& (2 ^ 4 - 1) = 0 := by
      simpa [BitVec.toNat_and] using congrArg BitVec.toNat hsp_al
    rwa [Nat.and_two_pow_sub_one_eq_mod] at ht
  have h20 : (sp_m + 0x20#64).toNat = sp_m.toNat + 32 :=
    BitVec.toNat_add_of_lt (by change sp_m.toNat + 32 < 2 ^ 64; omega)
  have h60 : (sp_m + 0x60#64).toNat = sp_m.toNat + 96 :=
    BitVec.toNat_add_of_lt (by change sp_m.toNat + 96 < 2 ^ 64; omega)
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem mainLocal96_eq (sp_m : BitVec 64) :
    stackAt (sp_m + 0x80#64) 96 =
      memRegion (sp_m + 0x20#64) 32 ∗
      memRegion (sp_m + 0x40#64) 8 ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64,
        ((sp_m + 0x48#64) ↦₆₄ c0) ∗ ((sp_m + 0x50#64) ↦₆₄ c1) ∗ ((sp_m + 0x58#64) ↦₆₄ c2)) ∗
      memRegion (sp_m + 0x60#64) 32 := by
  unfold stackAt
  have hbase : (sp_m + 0x80#64) - BitVec.ofNat 64 96 = sp_m + 0x20#64 := by bv_lin
  have hs96 : memRegion (sp_m + 0x20#64) 96 =
      memRegion (sp_m + 0x20#64) 32 ∗ memRegion (sp_m + 0x40#64) 64 := by
    simpa [show (sp_m + 0x20#64) + BitVec.ofNat 64 32 = sp_m + 0x40#64 by bv_lin] using
      memRegion_split (sp_m + 0x20#64) 32 64 (by decide)
  have hs64 : memRegion (sp_m + 0x40#64) 64 =
      memRegion (sp_m + 0x40#64) 8 ∗ memRegion (sp_m + 0x48#64) 56 := by
    simpa [show (sp_m + 0x40#64) + BitVec.ofNat 64 8 = sp_m + 0x48#64 by bv_lin] using
      memRegion_split (sp_m + 0x40#64) 8 56 (by decide)
  have hs56 : memRegion (sp_m + 0x48#64) 56 =
      memRegion (sp_m + 0x48#64) 24 ∗ memRegion (sp_m + 0x60#64) 32 := by
    simpa [show (sp_m + 0x48#64) + BitVec.ofNat 64 24 = sp_m + 0x60#64 by bv_lin] using
      memRegion_split (sp_m + 0x48#64) 24 32 (by decide)
  have hs24 : memRegion (sp_m + 0x48#64) 24 =
      memRegion (sp_m + 0x48#64) 8 ∗ memRegion (sp_m + 0x50#64) 16 := by
    simpa [show (sp_m + 0x48#64) + BitVec.ofNat 64 8 = sp_m + 0x50#64 by bv_lin] using
      memRegion_split (sp_m + 0x48#64) 8 16 (by decide)
  have hs16 : memRegion (sp_m + 0x50#64) 16 =
      memRegion (sp_m + 0x50#64) 8 ∗ memRegion (sp_m + 0x58#64) 8 := by
    simpa [show (sp_m + 0x50#64) + BitVec.ofNat 64 8 = sp_m + 0x58#64 by bv_lin] using
      memRegion_split (sp_m + 0x50#64) 8 8 (by decide)
  rw [hbase, hs96, hs64, hs56, hs24, hs16,
      memRegion_eight (sp_m + 0x48#64), memRegion_eight (sp_m + 0x50#64), memRegion_eight (sp_m + 0x58#64)]
  apply Entails.antisymm <;>
    (simp only [sepExists_sepConj_left, sepExists_sepConj_right]
     apply Entails.sepExists_elim; intro x0
     apply Entails.sepExists_elim; intro x1
     apply Entails.sepExists_elim; intro x2
     refine Entails.sepExists_right x2 (Entails.sepExists_right x1 (Entails.sepExists_right x0 ?_))
     sep_entail)

theorem mainLocal96_repack (sp_m c0 c1 c2 : BitVec 64) :
    memRegion (sp_m + 0x20#64) 32 ∗
      memRegion (sp_m + 0x40#64) 8 ∗
      ((sp_m + 0x48#64) ↦₆₄ c0) ∗ ((sp_m + 0x50#64) ↦₆₄ c1) ∗ ((sp_m + 0x58#64) ↦₆₄ c2) ∗
      memRegion (sp_m + 0x60#64) 32 ⊢
    stackAt (sp_m + 0x80#64) 96 := by
  rw [mainLocal96_eq sp_m]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2 (by sep_entail)))

theorem sepWP_let_cpu {P : Program} {target : BitVec 64} {s0 s1 : State} {Pre : SepProp}
    {post : State → SepProp → Prop} (hcpu : PureCpuStep s0 s1)
    (h : ∀ s1' : State, s1' = s1 → PureCpuStep s0 s1' → SepWP P target s1' Pre post) :
    SepWP P target s1 Pre post := h s1 rfl hcpu

theorem sepWP_let_nl {P : Program} {target : BitVec 64} {s0 s1 : State} {Pre : SepProp}
    {post : State → SepProp → Prop} (hnl : NlScanPreserved s0 s1)
    (h : ∀ s1' : State, s1' = s1 → NlScanPreserved s0 s1' → SepWP P target s1' Pre post) :
    SepWP P target s1 Pre post := h s1 rfl hnl

structure HbCmdCallees {P : Program} {L : Nat} (C : HbCliLayout)
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop)
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2) : Prop where
  hcCmd      : HbMainCmdCode P C
  hcSys      : HbSyscallsAndStderrCode P C
  hatom      : StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
                 C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr
  hv         : C.Valid
  hext       : ∀ pc, P.externAt? pc = none
  hsvc       : P.svc = Syscall.standard
  hNew       : subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_new")
                 (withCodeInv (HbAlloc.ofMallocng M γ CodeInv hCodeInv)
                   (hashbrownNewSpec C.hbPl (HbAlloc.ofMallocng M γ CodeInv hCodeInv)))
  hWithCap   : subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_with_capacity")
                 (withCodeInv (HbAlloc.ofMallocng M γ CodeInv hCodeInv)
                   (hashbrownWithCapacityInfallibleSpec C.hbPl (HbAlloc.ofMallocng M γ CodeInv hCodeInv)))
  hIns       : subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_insert")
                 (withCodeInv (HbAlloc.ofMallocng M γ CodeInv hCodeInv)
                   (hashbrownInsertInfallibleSpec C.hbPl (HbAlloc.ofMallocng M γ CodeInv hCodeInv)))
  hGet       : subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_get")
                 (withCodeInv (HbAlloc.ofMallocng M γ CodeInv hCodeInv)
                   (hashbrownGetSpec C.hbPl (HbAlloc.ofMallocng M γ CodeInv hCodeInv)))
  hContains  : subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_contains_key")
                 (withCodeInv (HbAlloc.ofMallocng M γ CodeInv hCodeInv)
                   (hashbrownContainsKeySpec C.hbPl (HbAlloc.ofMallocng M γ CodeInv hCodeInv)))
  hRem       : subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_remove")
                 (withCodeInv (HbAlloc.ofMallocng M γ CodeInv hCodeInv)
                   (hashbrownRemoveSpec C.hbPl (HbAlloc.ofMallocng M γ CodeInv hCodeInv)))
  hLen       : subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_len")
                 (withCodeInv (HbAlloc.ofMallocng M γ CodeInv hCodeInv)
                   (hashbrownLenSpec C.hbPl (HbAlloc.ofMallocng M γ CodeInv hCodeInv)))
  hIsEmpty   : subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_is_empty")
                 (withCodeInv (HbAlloc.ofMallocng M γ CodeInv hCodeInv)
                   (hashbrownIsEmptySpec C.hbPl (HbAlloc.ofMallocng M γ CodeInv hCodeInv)))
  hClear     : subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_clear")
                 (withCodeInv (HbAlloc.ofMallocng M γ CodeInv hCodeInv)
                   (hashbrownClearSpec C.hbPl (HbAlloc.ofMallocng M γ CodeInv hCodeInv)))
  hDrop      : subroutine_ok P (hashbrownLib.fnAddr C.hbMpl "hashbrown_drop")
                 (withCodeInv (HbAlloc.ofMallocng M γ CodeInv hCodeInv)
                   (hashbrownDropSpec C.hbPl (HbAlloc.ofMallocng M γ CodeInv hCodeInv)))
  hPrintBool : subroutine_ok P C.printBoolAddr (hbPrintBoolSpec C M γ)
  hPrintU64  : subroutine_ok P C.printU64Addr (hbPrintU64Spec C M γ)
  hPrintNone : subroutine_ok P C.stdioPrintAddr (hbStdioPrintNoneSpec C M γ)

/-! ## Command-Loop Print Call Wrappers -/

theorem stdout_cost_step (baseLc cm : Nat) (init : Bool) :
    (if init then baseLc + hbStdoutCost init + cm
     else (baseLc + hbStdoutCost init + cm) + mallocngBlockCost 1024) = baseLc + hbStdoutCost true + cm := by
  cases init <;> simp [hbStdoutCost]; omega

theorem stdout_blk_step (baseBlk bm_blk : Nat) (init : Bool) :
    (if init then baseBlk + hbStdoutBlocks init + bm_blk
     else (baseBlk + hbStdoutBlocks init + bm_blk) + 1) = baseBlk + hbStdoutBlocks true + bm_blk := by
  cases init <;> simp [hbStdoutBlocks]; omega

theorem call_hbPrintBool_loop {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target_pc ret_pc sp_m bm : BitVec 64} {haveLse : BitVec 8} {baseLc baseBlk u : Nat}
    {m : Map64} {b init : Bool} {e_err : BitVec 32} {c0 c1 c2 : BitVec 64}
    {s_ref s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hPrintBool : subroutine_ok P C.printBoolAddr (hbPrintBoolSpec C M γ))
    (hst : CmdLoopState C sp_m s_ref s) (hci : CodeInv s.mem)
    (hbudget : init = false →
      1024 ≤ (hbStdLimits L).maxReq ∧
      (baseLc + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm) + mallocngBlockCost 1024 ≤
        (hbStdLimits L).maxPeakCost ∧
      (baseBlk + tableAllocBlocks bm) + 1 ≤ (hbStdLimits L).maxPeakBlocks)
    (hpc : s.pc = C.printBoolAddr) (hrun : s.status = .Running)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = (if b then 1#64 else 0#64))
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running →
      CmdLoopState C sp_m s_ref sf → CalleeSavedPreserved s sf → CodeInv sf.mem →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stdout (formatBoolResult b) →
      SepWP P target_pc sf
        (CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u true e1 c0 c1 c2 sf ∗ F) post) :
    SepWP P target_pc s
      (CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 s ∗ F) post := by
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  have hstk : stackAt sp_m 4432 = memRegion (sp_m - 4432#64) 48 ∗ stackAt sp_m 4384 :=
    stackAt_split_bottom sp_m 4384 48 (by decide)
  refine sepWP_frozen_cut (mid := ret_pc) hCodeInv hci ?_
  refine SepWP.call_subroutine_frame hPrintBool
    (x := (b, init, baseLc + hbStdoutCost init + hbMapCost A bm,
           baseBlk + hbStdoutBlocks init + tableAllocBlocks bm, e_err, haveLse))
    (F := U64MapRep C.hbPl A (sp_m + 0x20#64) m bm u ∗
          (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbParseRoData C ∗
          (C.errInvalidCmdAddr ↦ᵣ errInvalidCmdBytes) ∗ (C.noneNlAddr ↦ᵣ noneNlBytes) ∗
          (C.nlByteAddr ↦ᵣ nlByteBytes) ∗ (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion (sp_m + 0x40#64) 8 ∗
          ((sp_m + 0x48#64) ↦₆₄ c0) ∗ ((sp_m + 0x50#64) ↦₆₄ c1) ∗ ((sp_m + 0x58#64) ↦₆₄ c2) ∗
          memRegion (sp_m + 0x60#64) 32 ∗ memRegion (sp_m + 0x98#64) 8 ∗
          memRegion (sp_m - 4432#64) 48 ∗ F)
    hpc hrun hst.2.1 hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ (by wp_close_oom_default)
  · intro R hm; dsimp only [hbPrintBoolSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, fun hi => ?_⟩, ?_⟩
    · subst hi; simpa [hbStdoutCost, hbStdoutBlocks] using hbudget rfl
    · dsimp only [CmdLoopRes, CmdLoopRest, HbCmdRoData] at hm
      rw [hstk] at hm; rw [hst.1]; exact (by sep_frame : _ → _) hm
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [hbPrintBoolSpec]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hfs, htr, hsig, htp⟩
    rw [stdout_cost_step baseLc (hbMapCost A bm) init,
        stdout_blk_step baseBlk (tableAllocBlocks bm) init, hst.1]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_left; intro e1
    refine SepWP.done hpc_f hrun_f fun hci_f =>
      SepWP.weaken_pre ?_ (hnext sf e1 hpc_f hrun_f
        (hst.of_cs_fs hsp_f hfs htp hsig hcs_f) hcs_f hci_f htr)
    dsimp only [CmdLoopRes, CmdLoopRest, HbCmdRoData]
    rw [hstk]; sep_entail

theorem call_hbPrintU64_loop {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target_pc ret_pc sp_m val bm : BitVec 64} {haveLse : BitVec 8} {baseLc baseBlk u : Nat}
    {m : Map64} {init : Bool} {e_err : BitVec 32} {c0 c1 c2 : BitVec 64}
    {s_ref s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hPrintU64 : subroutine_ok P C.printU64Addr (hbPrintU64Spec C M γ))
    (hst : CmdLoopState C sp_m s_ref s) (hci : CodeInv s.mem) (hsp_lo : 0x310 ≤ sp_m.toNat)
    (hbudget : init = false →
      1024 ≤ (hbStdLimits L).maxReq ∧
      (baseLc + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm) + mallocngBlockCost 1024 ≤
        (hbStdLimits L).maxPeakCost ∧
      (baseBlk + tableAllocBlocks bm) + 1 ≤ (hbStdLimits L).maxPeakBlocks)
    (hpc : s.pc = C.printU64Addr) (hrun : s.status = .Running)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hx0 : s.readReg64 .x0 = val)
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running →
      CmdLoopState C sp_m s_ref sf → CalleeSavedPreserved s sf → CodeInv sf.mem →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stdout (formatGetResult (some val)) →
      SepWP P target_pc sf
        (CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u true e1 c0 c1 c2 sf ∗ F) post) :
    SepWP P target_pc s
      (CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 s ∗ F) post := by
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  refine sepWP_frozen_cut (mid := ret_pc) hCodeInv hci ?_
  refine SepWP.call_subroutine_frame hPrintU64
    (x := (val, init, baseLc + hbStdoutCost init + hbMapCost A bm,
           baseBlk + hbStdoutBlocks init + tableAllocBlocks bm, e_err, haveLse))
    (F := U64MapRep C.hbPl A (sp_m + 0x20#64) m bm u ∗
          (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbParseRoData C ∗
          (C.falseNlAddr ↦ᵣ falseNlBytes) ∗ (C.trueNlAddr ↦ᵣ trueNlBytes) ∗
          (C.errInvalidCmdAddr ↦ᵣ errInvalidCmdBytes) ∗ (C.noneNlAddr ↦ᵣ noneNlBytes) ∗
          memRegion (sp_m + 0x40#64) 8 ∗
          ((sp_m + 0x48#64) ↦₆₄ c0) ∗ ((sp_m + 0x50#64) ↦₆₄ c1) ∗ ((sp_m + 0x58#64) ↦₆₄ c2) ∗
          memRegion (sp_m + 0x60#64) 32 ∗ memRegion (sp_m + 0x98#64) 8 ∗ F)
    hpc hrun hst.2.1 hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ (by wp_close_oom_default)
  · intro R hm; dsimp only [hbPrintU64Spec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, by rw [hst.1]; exact hsp_lo, fun hi => ?_⟩, ?_⟩
    · subst hi; simpa [hbStdoutCost, hbStdoutBlocks] using hbudget rfl
    · dsimp only [CmdLoopRes, CmdLoopRest, HbCmdRoData] at hm
      rw [hst.1]; exact (by sep_frame : _ → _) hm
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [hbPrintU64Spec]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hfs, htr, hsig, htp⟩
    rw [stdout_cost_step baseLc (hbMapCost A bm) init,
        stdout_blk_step baseBlk (tableAllocBlocks bm) init, hst.1]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_left; intro e1
    refine SepWP.done hpc_f hrun_f fun hci_f =>
      SepWP.weaken_pre ?_ (hnext sf e1 hpc_f hrun_f
        (hst.of_cs_fs hsp_f hfs htp hsig hcs_f) hcs_f hci_f htr)
    dsimp only [CmdLoopRes, CmdLoopRest, HbCmdRoData]; sep_entail

theorem call_hbPrintNone_loop {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target_pc ret_pc sp_m bm : BitVec 64} {haveLse : BitVec 8} {baseLc baseBlk u : Nat}
    {m : Map64} {init : Bool} {e_err : BitVec 32} {c0 c1 c2 : BitVec 64}
    {s_ref s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hPrintNone : subroutine_ok P C.stdioPrintAddr (hbStdioPrintNoneSpec C M γ))
    (hst : CmdLoopState C sp_m s_ref s) (hci : CodeInv s.mem)
    (hbudget : init = false →
      1024 ≤ (hbStdLimits L).maxReq ∧
      (baseLc + hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm) + mallocngBlockCost 1024 ≤
        (hbStdLimits L).maxPeakCost ∧
      (baseBlk + tableAllocBlocks bm) + 1 ≤ (hbStdLimits L).maxPeakBlocks)
    (hpc : s.pc = C.stdioPrintAddr) (hrun : s.status = .Running)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = C.noneNlAddr) (hx1 : s.readReg64 .x1 = 0x0b#64)
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running →
      CmdLoopState C sp_m s_ref sf → CalleeSavedPreserved s sf → CodeInv sf.mem →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stdout (formatGetResult none) →
      SepWP P target_pc sf
        (CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u true e1 c0 c1 c2 sf ∗ F) post) :
    SepWP P target_pc s
      (CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 s ∗ F) post := by
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  have hstk : stackAt sp_m 4432 = memRegion (sp_m - 4432#64) 48 ∗ stackAt sp_m 4384 :=
    stackAt_split_bottom sp_m 4384 48 (by decide)
  refine sepWP_frozen_cut (mid := ret_pc) hCodeInv hci ?_
  refine SepWP.call_subroutine_frame hPrintNone
    (x := (init, baseLc + hbStdoutCost init + hbMapCost A bm,
           baseBlk + hbStdoutBlocks init + tableAllocBlocks bm, e_err, haveLse))
    (F := U64MapRep C.hbPl A (sp_m + 0x20#64) m bm u ∗
          (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbParseRoData C ∗
          (C.falseNlAddr ↦ᵣ falseNlBytes) ∗ (C.trueNlAddr ↦ᵣ trueNlBytes) ∗
          (C.errInvalidCmdAddr ↦ᵣ errInvalidCmdBytes) ∗
          (C.nlByteAddr ↦ᵣ nlByteBytes) ∗ (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
          memRegion (sp_m + 0x40#64) 8 ∗
          ((sp_m + 0x48#64) ↦₆₄ c0) ∗ ((sp_m + 0x50#64) ↦₆₄ c1) ∗ ((sp_m + 0x58#64) ↦₆₄ c2) ∗
          memRegion (sp_m + 0x60#64) 32 ∗ memRegion (sp_m + 0x98#64) 8 ∗
          memRegion (sp_m - 4432#64) 48 ∗ F)
    hpc hrun hst.2.1 hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ (by wp_close_oom_default)
  · intro R hm; dsimp only [hbStdioPrintNoneSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, fun hi => ?_⟩, ?_⟩
    · subst hi; simpa [hbStdoutCost, hbStdoutBlocks] using hbudget rfl
    · dsimp only [CmdLoopRes, CmdLoopRest, HbCmdRoData] at hm
      rw [hstk] at hm; rw [hst.1]; exact (by sep_frame : _ → _) hm
  · intro sf hpc_f hrun_f hsp_f hcs_f; dsimp only [hbStdioPrintNoneSpec]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hfs, htr, hsig, htp⟩
    rw [stdout_cost_step baseLc (hbMapCost A bm) init,
        stdout_blk_step baseBlk (tableAllocBlocks bm) init, hst.1]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_left; intro e1
    refine SepWP.done hpc_f hrun_f fun hci_f =>
      SepWP.weaken_pre ?_ (hnext sf e1 hpc_f hrun_f
        (hst.of_cs_fs hsp_f hfs htp hsig hcs_f) hcs_f hci_f htr)
    dsimp only [CmdLoopRes, CmdLoopRest, HbCmdRoData]
    rw [hstk]; sep_entail

/-! ## Loop-Tail Branch and Invalid-Command Error Path -/

theorem tailAt0x17c_wp {P : Program} {C : HbCliLayout} {CodeInv : Memory → Prop}
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target sp_m nextPtr : BitVec 64} {hasMore : Bool} {s_ref s : State}
    {Pre : State → SepProp} {post : State → SepProp → Prop}
    (hcCmd : HbMainCmdCode P C) (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hPre : ∀ {s1 s2 : State}, s2.tpidrEl0 = s1.tpidrEl0 → VmFieldsPreserved s1 s2 → Pre s1 ⊢ Pre s2)
    (hpc : s.pc = C.std.userMainAddr + 0x17c#64) (hrun : s.status = .Running)
    (hst : CmdLoopState C sp_m s_ref s) (hci : CodeInv s.mem)
    (hx27 : s.readReg64 .x27 = nextPtr)
    (hx26 : s.readReg64 .x26 = if hasMore then 0#64 else 1#64)
    (hNext : ∀ sf : State,
      sf.pc = (if hasMore then C.std.userMainAddr + 0x184#64 else C.std.userMainAddr + 0x300#64) →
      sf.status = .Running → CmdLoopState C sp_m s_ref sf → CodeInv sf.mem →
      sf.trace = s.trace → sf.readReg64 .x0 = nextPtr → sf.readReg64 .x22 = s.readReg64 .x22 →
      SepWP P target sf (Pre sf) post) :
    SepWP P target s (Pre s) post := by
  refine sepWP_cpu_cut
    (mid := if hasMore then C.std.userMainAddr + 0x184#64 else C.std.userMainAddr + 0x300#64)
    hCodeInv hci hext hsvc ?_
  have hc' := (hcCmd.withSvc nonVmSvc).rustMainLoop; unpack_loop_code hc'
  rcases hst with ⟨hsp, hsp_al, hfs, htp, hsig, hvregs, r19, r20, r23, r24, r25, r28, r29⟩
  cases hasMore
  · simp only [Bool.false_eq_true, ↓reduceIte] at hx26 ⊢
    have hx26' : s.readReg64 (.gpr 26#5) = 1#64 := hx26
    wp_steps 2
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) fun hvm1 hci1 => ?_
    refine SepWP.weaken_pre (hPre (by simp [wp_norm, arm64_norm]) hvm1)
      (hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) ?_ hci1 (by simp [wp_norm, arm64_norm]) wp_a wp_a)
    exact ⟨by simp [wp_norm, arm64_norm, hsp], by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al,
      by simp [wp_norm, arm64_norm, hfs], by simp [wp_norm, arm64_norm, htp],
      by simp [wp_norm, arm64_norm, hsig], by simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregs],
      wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a⟩
  · simp only [↓reduceIte] at hx26 ⊢
    have hx26' : s.readReg64 (.gpr 26#5) = 0#64 := hx26
    wp_steps 2
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) fun hvm1 hci1 => ?_
    refine SepWP.weaken_pre (hPre (by simp [wp_norm, arm64_norm]) hvm1)
      (hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) ?_ hci1 (by simp [wp_norm, arm64_norm]) wp_a wp_a)
    exact ⟨by simp [wp_norm, arm64_norm, hsp], by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al,
      by simp [wp_norm, arm64_norm, hfs], by simp [wp_norm, arm64_norm, htp],
      by simp [wp_norm, arm64_norm, hsig], by simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregs],
      wp_a, wp_a, wp_a, wp_a, wp_a, wp_a, wp_a⟩

private theorem errAt0x220_prep_wp {P : Program} {C : HbCliLayout} {CodeInv : Memory → Prop}
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target v98 : BitVec 64} {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (hcCmd : HbMainCmdCode P C) (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hpc : s.pc = C.std.userMainAddr + 0x220#64) (hrun : s.status = .Running) (hci : CodeInv s.mem)
    (hNext : ∀ s1 : State,
      s1.pc = C.stderrWriteAllAddr → s1.status = .Running →
      PureCpuStep s s1 → VmFieldsPreserved s s1 → CodeInv s1.mem →
      s1.readReg64 Reg.lr = C.std.userMainAddr + 0x234#64 →
      s1.readReg64 .x0 = s.readReg64 .x29 + 0x18#64 →
      s1.readReg64 .x1 = s.readReg64 .x19 →
      s1.readReg64 .x2 = 23#64 →
      SepWP P target s1 (((s.readReg64 .x29 + 0x18#64) ↦₆₄ s.readReg64 .x23) ∗ Rest) post) :
    SepWP P target s (((s.readReg64 .x29 + 0x18#64) ↦₆₄ v98) ∗ Rest) post := by
  refine sepWP_cpu_cut (mid := C.stderrWriteAllAddr) hCodeInv hci hext hsvc ?_
  have hc' := (hcCmd.withSvc nonVmSvc).rustMainLoop; unpack_loop_code hc'
  dsimp only [Reg.x29, Reg.x23, Reg.x19, Reg.x0, Reg.x1, Reg.x2, Reg.lr] at *
  wp_steps 4; wp_steps 1
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) fun hvm1 hci1 =>
    hNext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) (close_cpu_step s) hvm1 hci1
      wp_a wp_a wp_a wp_a

private theorem errAt0x234_wp {P : Program} {C : HbCliLayout} {CodeInv : Memory → Prop}
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target sp_m nextPtr : BitVec 64} {hasMore : Bool} {s_ref s : State}
    {Pre : State → SepProp} {post : State → SepProp → Prop}
    (hcCmd : HbMainCmdCode P C) (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hPre : ∀ {s1 s2 : State}, s2.tpidrEl0 = s1.tpidrEl0 → VmFieldsPreserved s1 s2 → Pre s1 ⊢ Pre s2)
    (hpc : s.pc = C.std.userMainAddr + 0x234#64) (hrun : s.status = .Running)
    (hst : CmdLoopState C sp_m s_ref s) (hci : CodeInv s.mem)
    (hx0 : s.readReg64 .x0 = 0#64) (hx27 : s.readReg64 .x27 = nextPtr)
    (hx26 : s.readReg64 .x26 = if hasMore then 0#64 else 1#64)
    (hNext : ∀ sf : State,
      sf.pc = (if hasMore then C.std.userMainAddr + 0x184#64 else C.std.userMainAddr + 0x300#64) →
      sf.status = .Running → CmdLoopState C sp_m s_ref sf → CodeInv sf.mem →
      sf.trace = s.trace → sf.readReg64 .x0 = nextPtr → sf.readReg64 .x22 = s.readReg64 .x22 →
      SepWP P target sf (Pre sf) post) :
    SepWP P target s (Pre s) post := by
  refine sepWP_cpu_cut (mid := C.std.userMainAddr + 0x17c#64) hCodeInv hci hext hsvc ?_
  have hc' := (hcCmd.withSvc nonVmSvc).rustMainLoop; unpack_loop_code hc'
  have hx0' : s.readReg64 (.gpr 0#5) = 0#64 := hx0
  wp_steps 1
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) fun hvm1 hci1 => ?_
  refine sepWP_let_cpu (s0 := s) (close_cpu_step s) fun s1 hs1_eq hcpu1 => ?_
  rw [← hs1_eq] at hvm1 hci1
  refine SepWP.weaken_pre (hPre hcpu1.2.2.2.1.1 hvm1) ?_
  exact tailAt0x17c_wp hCodeInv hcCmd hext hsvc hPre
    (by rw [hs1_eq]; exact wp_a) (by rw [hs1_eq]; simp [wp_norm, arm64_norm, hrun])
    (hst.of_cpu hcpu1) hci1
    (hcpu1.2.2.2.2.readReg64_x27.trans hx27)
    (hcpu1.2.2.2.2.readReg64_x26.trans hx26)
    fun sf hpc_f hrun_f hst_f hci_f htr_f hx0_f hx22_f =>
      hNext sf hpc_f hrun_f hst_f hci_f (htr_f.trans hcpu1.2.2.1) hx0_f
        (hx22_f.trans hcpu1.2.2.2.2.readReg64_x22)

theorem errAt0x220_wp {P : Program} {C : HbCliLayout} {L : Nat}
    (M : MallocngCoreIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    (CodeInv : Memory → Prop) (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {target sp_m nextPtr bm : BitVec 64} {haveLse : BitVec 8} {baseLc baseBlk u : Nat}
    {m : Map64} {init hasMore : Bool} {e_err : BitVec 32} {c0 c1 c2 : BitVec 64}
    {s_ref s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hcCmd : HbMainCmdCode P C) (hcSys : HbSyscallsAndStderrCode P C)
    (hatom : StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr)
    (hv : C.Valid) (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hpc : s.pc = C.std.userMainAddr + 0x220#64) (hrun : s.status = .Running)
    (hst : CmdLoopState C sp_m s_ref s) (hci : CodeInv s.mem)
    (hx27 : s.readReg64 .x27 = nextPtr)
    (hx26 : s.readReg64 .x26 = if hasMore then 0#64 else 1#64)
    (hNext : ∀ sf : State,
      sf.pc = (if hasMore then C.std.userMainAddr + 0x184#64 else C.std.userMainAddr + 0x300#64) →
      sf.status = .Running → CmdLoopState C sp_m s_ref sf → CodeInv sf.mem →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stderr errInvalidCmdBytes →
      sf.readReg64 .x0 = nextPtr → sf.readReg64 .x22 = s.readReg64 .x22 →
      SepWP P target sf
        (CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 sf ∗ F) post) :
    SepWP P target s
      (CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 s ∗ F) post := by
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  have hx19 : s.readReg64 .x19 = C.errInvalidCmdAddr := hst.2.2.2.2.2.2.1
  have hx23 : s.readReg64 .x23 = C.stderrGlobalAddr := hst.2.2.2.2.2.2.2.2.1
  have hx29 : s.readReg64 .x29 = sp_m + 0x80#64 := hst.2.2.2.2.2.2.2.2.2.2.2.2
  have h98_eq : sp_m + 0x98#64 = s.readReg64 .x29 + 0x18#64 := by rw [hx29]; bv_lin
  have hopen :
      CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 s ∗ F ⊢
      ∃∗ v98 : BitVec 64,
        ((s.readReg64 .x29 + 0x18#64) ↦₆₄ v98) ∗
        (U64MapRep C.hbPl A (sp_m + 0x20#64) m bm u ∗
         M.Heap γ (baseLc + hbStdoutCost init + hbMapCost A bm)
                  (baseBlk + hbStdoutBlocks init + tableAllocBlocks bm) s ∗
         HbStdoutInv C M γ init ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
         HbCmdRoData C ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
         HbThreadIdInv C s.tpidrEl0 ∗ (muslErrnoAddr s ↦₃₂ e_err) ∗
         memRegion (sp_m + 0x40#64) 8 ∗
         ((sp_m + 0x48#64) ↦₆₄ c0) ∗ ((sp_m + 0x50#64) ↦₆₄ c1) ∗ ((sp_m + 0x58#64) ↦₆₄ c2) ∗
         memRegion (sp_m + 0x60#64) 32 ∗ stackAt sp_m 4432 ∗ F) := by
    dsimp only [CmdLoopRes, CmdLoopRest]
    rw [memRegion_eight (sp_m + 0x98#64), h98_eq]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    exact Entails.sepExists_elim fun v98 => Entails.sepExists_right v98 (by sep_entail)
  refine SepWP.weaken_pre hopen ?_
  apply SepWP.exists_left; intro v98
  refine errAt0x220_prep_wp hCodeInv hcCmd hext hsvc hpc hrun hci
    fun s1 hpc1 hrun1 hcpu1 hvm1 hci1 hlr1 hx0_1 hx1_1 hx2_1 => ?_
  have hst1 : CmdLoopState C sp_m s_ref s1 := hst.of_cpu hcpu1
  have hstk4432 : stackAt sp_m 4432 = memRegion (sp_m - 4432#64) 4176 ∗ stackAt sp_m 256 :=
    stackAt_split_bottom sp_m 256 4176 (by decide)
  have herr1 : muslErrnoAddr s = muslErrnoAddr s1 := by simp [muslErrnoAddr, hcpu1.2.2.2.1.1]
  have hht1 : M.Heap γ (baseLc + hbStdoutCost init + hbMapCost A bm)
      (baseBlk + hbStdoutBlocks init + tableAllocBlocks bm) s ⊢
      M.Heap γ (baseLc + hbStdoutCost init + hbMapCost A bm)
      (baseBlk + hbStdoutBlocks init + tableAllocBlocks bm) s1 :=
    M.heap_transport hvm1.brk_eq hvm1.brkStart_eq hvm1.physMemAvail_eq hvm1.perm_eq
  refine call_hbStderrWriteAll (ret_pc := C.std.userMainAddr + 0x234#64)
    (selfPtr := sp_m + 0x98#64) (msgPtr := C.errInvalidCmdAddr) (msgBytes := errInvalidCmdBytes) (haveLse := haveLse)
    (F := U64MapRep C.hbPl A (sp_m + 0x20#64) m bm u ∗
      M.Heap γ (baseLc + hbStdoutCost init + hbMapCost A bm)
               (baseBlk + hbStdoutBlocks init + tableAllocBlocks bm) s ∗
      HbStdoutInv C M γ init ∗ HbParseRoData C ∗
      (C.falseNlAddr ↦ᵣ falseNlBytes) ∗ (C.trueNlAddr ↦ᵣ trueNlBytes) ∗
      (C.noneNlAddr ↦ᵣ noneNlBytes) ∗ (C.nlByteAddr ↦ᵣ nlByteBytes) ∗
      (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
      StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
      HbAdapterWriteVtableRo C ∗ (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (muslErrnoAddr s1 ↦₃₂ e_err) ∗
      memRegion (sp_m + 0x40#64) 8 ∗
      ((sp_m + 0x48#64) ↦₆₄ c0) ∗ ((sp_m + 0x50#64) ↦₆₄ c1) ∗ ((sp_m + 0x58#64) ↦₆₄ c2) ∗
      memRegion (sp_m + 0x60#64) 32 ∗ memRegion (sp_m - 4432#64) 4176 ∗ F)
    true hcSys hatom hv.stderrGlobal_align hv.threadIdCtr_align hsvc hext (by decide) (by decide) hv.errInv_noWrap ?_ ?_
    hpc1 hrun1 hst1.2.1 hlr1 (hx0_1.trans h98_eq.symm) (hx1_1.trans hx19) hx2_1
  · intro R hm
    dsimp only [HbCmdRoData, hbBytesSlice] at hm ⊢
    rw [← h98_eq, hx23, herr1, ← hcpu1.2.2.2.1.1, hstk4432] at hm
    rw [hst1.1]; exact (by sep_frame : _ → _) hm
  · intro s2 hpc2 hrun2 hsp2 hcs2 hx0_2 hfs2 htr2 hnv2
    have hst2 : CmdLoopState C sp_m s_ref s2 :=
      hst1.of_cs_fs hsp2 hfs2 hnv2.tpidrEl0_eq hnv2.sigActions_eq hcs2
    have hci2 : CodeInv s2.mem := hCodeInv hnv2.keepsFrozen hci1
    have herr2 : muslErrnoAddr s1 = muslErrnoAddr s2 := by simp [muslErrnoAddr, hnv2.tpidrEl0_eq]
    have hht12 := Entails.trans hht1 (hnv2.heap_transport M (γ := γ)
      (lc := baseLc + hbStdoutCost init + hbMapCost A bm)
      (blk := baseBlk + hbStdoutBlocks init + tableAllocBlocks bm))
    have h98_mem := pointsTo64_entails_memRegion (sp_m + 0x98#64) C.stderrGlobalAddr
    have hrepack :
        (((sp_m + 0x98#64) ↦₆₄ C.stderrGlobalAddr) ∗
         (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
         hbBytesSlice true C.errInvalidCmdAddr errInvalidCmdBytes ∗
         HbThreadIdInv C s1.tpidrEl0 ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
         (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ stackAt s1.sp 256) ∗
        (U64MapRep C.hbPl A (sp_m + 0x20#64) m bm u ∗
         M.Heap γ (baseLc + hbStdoutCost init + hbMapCost A bm)
                  (baseBlk + hbStdoutBlocks init + tableAllocBlocks bm) s ∗
         HbStdoutInv C M γ init ∗ HbParseRoData C ∗
         (C.falseNlAddr ↦ᵣ falseNlBytes) ∗ (C.trueNlAddr ↦ᵣ trueNlBytes) ∗
         (C.noneNlAddr ↦ᵣ noneNlBytes) ∗ (C.nlByteAddr ↦ᵣ nlByteBytes) ∗
         (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
         StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
         HbAdapterWriteVtableRo C ∗ (C.captureUsedAddr ↦₈ᵣ 0#8) ∗ (muslErrnoAddr s1 ↦₃₂ e_err) ∗
         memRegion (sp_m + 0x40#64) 8 ∗
         ((sp_m + 0x48#64) ↦₆₄ c0) ∗ ((sp_m + 0x50#64) ↦₆₄ c1) ∗ ((sp_m + 0x58#64) ↦₆₄ c2) ∗
         memRegion (sp_m + 0x60#64) 32 ∗ memRegion (sp_m - 4432#64) 4176 ∗ F) ⊢
        CmdLoopRes C M γ CodeInv hCodeInv sp_m haveLse baseLc baseBlk m bm u init e_err c0 c1 c2 s2 ∗ F := by
      dsimp only [CmdLoopRes, CmdLoopRest, HbCmdRoData, hbBytesSlice]
      rw [herr2, ← hnv2.tpidrEl0_eq, hst1.1, hstk4432]
      exact Entails.trans (sepConj_mono (sepConj_mono_left h98_mem)
        (sepConj_mono_right (sepConj_mono_left hht12))) (by sep_entail)
    refine SepWP.weaken_pre hrepack ?_
    exact errAt0x234_wp hCodeInv hcCmd hext hsvc
      (fun htp hvm => sepConj_mono_left (CmdLoopRes.transport htp hvm))
      hpc2 hrun2 hst2 hci2 hx0_2
      (hcs2.readReg64_x27.trans (hcpu1.2.2.2.2.readReg64_x27.trans hx27))
      (hcs2.readReg64_x26.trans (hcpu1.2.2.2.2.readReg64_x26.trans hx26))
      fun sf hpc_f hrun_f hst_f hci_f htr_f hx0_f hx22_f =>
        hNext sf hpc_f hrun_f hst_f hci_f
          (by rw [htr_f, htr2, hcpu1.2.2.1]) hx0_f
          (hx22_f.trans (hcs2.readReg64_x22.trans hcpu1.2.2.2.2.readReg64_x22))

end CaseStudies.Hashbrown.Proofs.StdCli
