/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import CaseStudies.Hashbrown.Proofs.StdCli.StartupPreStage12
import CaseStudies.Hashbrown.Proofs.StdCli.StartupPreLangStartMain
import CaseStudies.Hashbrown.Proofs.StdCli.MallocngBridge

/-!
# Pre-Main Startup Composition

Composes ELF process startup (`_start`, `c_main`, `std::rt::lang_start_internal`) with tracked
`mallocng` heap initialization up to `userMain` entry (`hbStartup_to_userMain`).
-/

set_option autoImplicit false

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64
open Arm64.Process
open ProofLib
open ProofLib.StdStartup
open VerifiedLibraries.Mallocng

structure HbUserMainState (P : Program) (L : StdBinaryLayout) (img : ElfImage)
    (inputs : ProcessInputs) (s0 s_main : State) : Prop where
  codeLoaded   : P.CodeLoaded s_main.mem
  keepsFrozen  : s0.mem.KeepsFrozen s_main.mem
  pc_eq        : s_main.pc = L.userMainAddr
  status_eq    : s_main.status = .Running
  sp_eq        : s_main.sp = (StackLayout.of img inputs).sp0 - 0x170#64
  spAligned_eq : s_main.spAligned = true
  sp_headroom  : 261984 ≤ s_main.sp.toNat
  sp_userVa    : s_main.sp.toNat ≤ Arm64.USER_VA_LIMIT
  lr_eq        : s_main.readReg64 .lr = L.beginShortBacktraceAddr + 0x0c#64
  tpidr_eq     : s_main.tpidrEl0 = L.builtinTlsAddr + 0xc8#64
  fs_eq        : s_main.fs = initFsState inputs
  trace_eq     : s_main.trace = []

abbrev HbAltstackMappedPre (altOpt : Option (BitVec 64 × Nat)) : SepProp :=
  match altOpt with
  | none => emp
  | some (altBase, altRawSz) => memMapped altBase (4096 + altRawSz)

private theorem hbStack_s0_split (sp0 : BitVec 64) :
    memRegion (sp0 - BitVec.ofNat 64 HbInitialStackScratchBytes) HbInitialStackScratchBytes =
      memRegion (sp0 - 524288#64) 523744 ∗
      memRegion (sp0 - 0x220#64) 0x60 ∗
      memRegion (sp0 - 0x1c0#64) 0x1c0 := by
  change memRegion (sp0 - 524288#64) 524288 = _
  have s1 := memRegion_split_le (sp0 - 524288#64) 523744 524288 (by decide) (by decide)
  rw [show (sp0 - 524288#64) + BitVec.ofNat 64 523744 = sp0 - 0x220#64 by bv_lin,
      show (524288 - 523744 : Nat) = 0x220 from rfl] at s1
  have s2 := memRegion_split_le (sp0 - 0x220#64) 0x60 0x220 (by decide) (by decide)
  rw [show (sp0 - 0x220#64) + BitVec.ofNat 64 0x60 = sp0 - 0x1c0#64 by bv_lin,
      show (0x220 - 0x60 : Nat) = 0x1c0 from rfl] at s2
  rw [s1, s2]

private theorem hbStack_cm_split (sp0 : BitVec 64) :
    memRegion (sp0 - 524288#64) 523744 ∗ memRegion (sp0 - 0x220#64) 0x1f0 =
      memRegion (sp0 - 524288#64) 523408 ∗ stackAt (sp0 - 0x30#64) 0x340 := by
  have s1 := memRegion_split_le (sp0 - 524288#64) 523744 524240 (by decide) (by decide)
  rw [show (sp0 - 524288#64) + BitVec.ofNat 64 523744 = sp0 - 0x220#64 by bv_lin,
      show (524240 - 523744 : Nat) = 0x1f0 from rfl] at s1
  have s2 := memRegion_split_le (sp0 - 524288#64) 523408 524240 (by decide) (by decide)
  rw [show (sp0 - 524288#64) + BitVec.ofNat 64 523408 = (sp0 - 0x30#64) - BitVec.ofNat 64 0x340 by bv_lin,
      show (524240 - 523408 : Nat) = 0x340 from rfl] at s2
  dsimp only [stackAt]
  rw [← s1, s2]

private theorem hbStack_main_split (sp0 : BitVec 64) :
    memRegion (sp0 - 524288#64) 523408 ∗ stackAt (sp0 - 0x170#64) 0x200 =
      stackAt ((sp0 - 0x170#64) - 261984#64) 261936 ∗ stackAt (sp0 - 0x170#64) 261984 := by
  dsimp only [stackAt]
  rw [show (sp0 - 0x170#64) - BitVec.ofNat 64 0x200 = sp0 - 0x370#64 by bv_lin,
      show ((sp0 - 0x170#64) - 261984#64) - BitVec.ofNat 64 261936 = sp0 - 524288#64 by bv_lin,
      show (sp0 - 0x170#64) - BitVec.ofNat 64 261984 = (sp0 - 0x170#64) - 261984#64 from rfl]
  have s1 := memRegion_split_le (sp0 - 524288#64) 523408 523920 (by decide) (by decide)
  rw [show (sp0 - 524288#64) + BitVec.ofNat 64 523408 = sp0 - 0x370#64 by bv_lin,
      show (523920 - 523408 : Nat) = 0x200 from rfl] at s1
  have s2 := memRegion_split_le (sp0 - 524288#64) 261936 523920 (by decide) (by decide)
  rw [show (sp0 - 524288#64) + BitVec.ofNat 64 261936 = (sp0 - 0x170#64) - 261984#64 by bv_lin,
      show (523920 - 261936 : Nat) = 261984 from rfl] at s2
  rw [← s1, s2]

local macro "hb_top_wp_simp" : tactic => `(tactic|
  simp (config := { decide := true }) [State.stepExclOracle, State.stepExclLoop, State.readReg32,
    wp_norm, arm64_norm, bv_lin_norm, *])

private theorem hb_top_nv_of_eq {a b : State}
    (h1 : b.fs = a.fs) (h2 : b.trace = a.trace) (h3 : b.tpidrEl0 = a.tpidrEl0)
    (h4 : b.sigActions = a.sigActions) (h5 : b.sigAltStack = a.sigAltStack) :
    HbNonVmFields a b :=
  ⟨h1, h2, h3, h4, h5⟩

local macro "hb_top_nv_rfl " s:term : tactic => `(tactic|
  refine hb_top_nv_of_eq (a := $s) ?_ ?_ ?_ ?_ ?_ <;>
    simp [wp_norm, arm64_norm, State.stepExclOracle, State.stepExclLoop])

private theorem hb_top_evalSvc_rt_sigaction {P : Program} {s : State}
    (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc) (hx8 : s.readReg64 .x8 = 134#64) :
    P.evalInst (.system false 0#16) s = execRtSigaction s := by
  rcases hsvc with h | h
  · rw [_root_.Arm64.Program.evalInst_svc0, h, evalSvc_standard]
    simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable,
      Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, hx8]
  · rw [_root_.Arm64.Program.evalInst_svc0, h, evalSvc_nonVmSvc]
    simp [nonVmSvc, nonVmSyscallTable, Syscall.dispatch, Syscall.stdioTable,
      Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.signalsTable, hx8]

private theorem hb_top_fourCells_eq_bytes (a v0 v1 v2 v3 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3)) =
      (a ↦ₛ (unpack64 v0 ++ unpack64 v1 ++ unpack64 v2 ++ unpack64 v3)) := by
  simp only [pointsToBytes_append, List.length_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
  rw [show a + BitVec.ofNat 64 (8 + 8) = a + 16#64 by bv_lin,
      show a + BitVec.ofNat 64 (8 + 8 + 8) = a + 24#64 by bv_lin]
  ac_rfl

section
arm64_proof_prelude

private theorem hb_top_step_str64_perm {prog : Program} {target_pc pc ea val : BitVec 64} {s : State} {P P' : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .X64 rt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val) (hstore : SepStore64 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP; intro R hm; let m' := s.mem.write64 ea val; have hm' := hstore.store hm; have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; have hn := hnext m' (Memory.perm_write64 s.mem ea val); unfold SepWP at hn; exact hn R hm'

private theorem hb_top_step_stp64_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64} {s : State} {P P1 P2 : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2) (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP; intro R hm; let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 := hstore1.store hm; have hm2 := hstore2.store hm1; have hcan1 := hstore1.writable hm; have hcan2 := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m2 := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]; have hn := hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1)); unfold SepWP at hn; exact hn R hm2

private theorem step_hb_top_syscallRet_zero {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64}
    (hcode : P.hasCode L.syscallRetAddr syscallRetNonnegWords) {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ stackAt s.sp 0x20 ∗ (F ∗ R))
    (hpc : s.pc = L.syscallRetAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 0#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → HbNonVmFields s sf →
      SepWP P target_pc sf (stackAt s.sp 0x20 ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame (P' := stackAt s.sp 0x20 ∗ F) (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have hhi : ConditionHolds .HI (addsPState64 0#64 4096#64) = false := by
    unfold addsPState64 ConditionHolds; dsimp [AddWithCarry64]; decide
  have hsp_sub_al : ((s.sp - 32#64) &&& 0xf#64 == 0#64) = true := by simpa using s.spAligned_sub 0x20#64 hsp_align
  rw [stackAt_eq_cells s.sp 4]; unfold_stack_cells 4
  have hf0 : P.fetch L.syscallRetAddr = some (.stp .W64 .x29 .lr (.PreIndex .sp 0xffffffffffffffe0#64)) :=
    Program.fetch_of_hasCode_decodeAt 0 hcode (by bv_lin) (by decide)
  have hf3 : P.fetch (L.syscallRetAddr + 12#64) = some (.str .X64 (.gpr 19#5) (.Offset .sp 16#64)) :=
    Program.fetch_of_hasCode_decodeAt 3 hcode (by bv_lin) (by decide)
  refine hb_top_step_stp64_perm (ea2 := s.sp - 24#64) hpc hrun hf0
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_align])
    (show evalAddrMode s (.PreIndex .sp 0xffffffffffffffe0#64) = (s.sp - 32#64, some (.sp, s.sp - 32#64)) by
      simp [evalAddrMode, arm64_norm, bv_lin_norm])
    (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m1 _ => ?_
  wp_steps 2
  refine hb_top_step_str64_perm (ea := s.sp - 16#64) (wb := none) (val := s.readReg64 (.gpr 19#5))
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf3
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, wp_norm, arm64_norm] using hsp_sub_al)
    (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm])
    (by wp_sep_access) fun m2 _ => ?_
  wp_steps 5
  refine SepWP.weaken_pre_frame (P' := stackAt s.sp 0x20 ∗ F)
    (fun R hm => by rw [stackAt_eq_cells s.sp 4] at *; fold_stack_cells) ?_
  refine hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simpa [State.spAligned, wp_norm, arm64_norm, bv_lin_norm] using hsp_align)
    (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hx0]) (by hb_top_nv_rfl s)

set_option maxHeartbeats 400000 in
private theorem step_hb_libcSigaction_probe_zero {P : Program} {L : StdBinaryLayout} {target_pc ret_pc sig : BitVec 64}
    (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc) (hhead : P.hasCode L.libcSigactionAddr libcSigactionHeadWords)
    (htail : hasInstrs P (L.libcSigactionAddr + 0xfc#64) (libcSigactionIgnTailInstrs L))
    (hret : P.hasCode L.syscallRetAddr syscallRetNonnegWords) (hmemcpy : hasInstrs P L.memcpyAddr hbMemcpyInstrs)
    {s : State} {oact v0 v1 v17 : BitVec 64} {G : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = L.libcSigactionAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hsp_lo : 0x90 ≤ s.sp.toNat)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = sig) (hx1 : s.readReg64 .x1 = 0#64) (hx2 : s.readReg64 .x2 = oact)
    (hsig_mem : sig = 11#64 ∨ sig = 7#64) (hoact_ne : oact ≠ 0#64) (hsig0 : s.getSigAction (sig.truncate 32) = {})
    (hv17_hi : v17.extractLsb' 32 32 = 0#32)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → HbNonVmFields s sf →
      SepWP P target_pc sf ((((oact ↦₆₄ 0#64) ∗ ((oact + 8#64) ↦₆₄ 0#64) ∗ ((oact + 0x88#64) ↦₆₄ 0#64)) ∗ stackAt s.sp 0x90) ∗ G) post oom) :
    SepWP P target_pc s ((((oact ↦₆₄ v0) ∗ ((oact + 8#64) ↦₆₄ v1) ∗ ((oact + 0x88#64) ↦₆₄ v17)) ∗ stackAt s.sp 0x90) ∗ G) post oom := by
  have hret' := hret
  have hsig0' : s.sigActions (sig.truncate 32) = {} := hsig0
  refine SepWP.weaken_pre_frame
    (P' := (((oact ↦₆₄ v0) ∗ memRegion (oact + 8#64) 8 ∗ ((oact + 0x88#64) ↦₃₂ v17.extractLsb' 0 32)) ∗ stackAt s.sp 0x90) ∗
      (((oact + 0x88#64 + 4#64) ↦₃₂ 0#32) ∗ G))
    (fun R hm => by
      rw [pointsTo64_split32 (oact + 0x88#64) v17, hv17_hi] at hm
      rw [memRegion_eight]; revert hm; sep_frame) ?_
  have hp := htail; dsimp only [libcSigactionIgnTailInstrs] at hp; generalize hb : L.libcSigactionAddr + 0xfc#64 = b at hp
  have_instrs hp 0 43; clear hp htail
  have hsp_sub_al : ((s.sp + 0xffffffffffffff90#64) &&& 0xf#64 == 0#64) = true := by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x70#64 hsp_align
  have hsxtw : (sig >>> 0 &&& 0xffffffff#64 ||| (if sig.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&& 0xffffffff00000000#64) = sig := by
    rcases hsig_mem with rfl | rfl <;> decide
  have hlo : 1 ≤ (sig.truncate 32).toNat := by rcases hsig_mem with rfl | rfl <;> decide
  have hhi : (sig.truncate 32).toNat ≤ 64 := by rcases hsig_mem with rfl | rfl <;> decide
  have ho_bne : (oact != 0#64) = true := bne_iff_ne.mpr hoact_ne
  wp_conv_pre => rw [stackAt_split_cells s.sp 0x20 14 (by decide), cells_split_sub s.sp 112 32 10 4]; simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun w10 => SepWP.exists_elim fun w11 => SepWP.exists_elim fun w12 => SepWP.exists_elim fun w13 => ?_
  iterate 10 (refine SepWP.exists_elim fun _ => ?_)
  clear hret; wp_steps 9; clear hhead
  have hpc_b17 : L.libcSigactionAddr + 320#64 = b + 68#64 := by rw [← hb]; bv_lin
  conv => arg 3; rw [hpc_b17]
  wp_steps 6
  have ho_f : ((s.sp - 32#64) == 0#64) = false := beq_false_of_ne (by bv_omega)
  have ko1 : (s.sp - 32#64) + 8#64 = s.sp - 24#64 := by bv_lin
  have ko2 : (s.sp - 32#64) + 16#64 = s.sp - 16#64 := by bv_lin
  have ko3 : (s.sp - 32#64) + 24#64 = s.sp - 8#64 := by bv_lin
  refine SepWP.weaken_pre_frame
    (P' := kSigActionAt 0#64 0#64 0#64 0#64 0#64 ∗
      (optOldSigActionAt (s.sp - 32#64) (unpack64 w10 ++ unpack64 w11 ++ unpack64 w12 ++ unpack64 w13) ∗ ?_))
    (fun R hm => by
      dsimp only [kSigActionAt, optOldSigActionAt]; rw [ho_f]
      simp only [beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, emp_sepConj, ← hb_top_fourCells_eq_bytes]
      rw [ko1, ko2, ko3]; revert hm; sep_frame) ?_
  refine SepWP.step_svc_rt_sigaction (pc := b + 92#64) (signum := sig.truncate 32) (act := 0#64)
    (handler := 0#64) (flags := 0#64) (restorer := 0#64) (mask := 0#64)
    (oldact := s.sp - 32#64) (oldBs₀ := unpack64 w10 ++ unpack64 w11 ++ unpack64 w12 ++ unpack64 w13)
    (by hb_top_wp_simp) (by hb_top_wp_simp) hf_23 (by hb_top_wp_simp) (by hb_top_wp_simp) (by hb_top_wp_simp)
    (by hb_top_wp_simp) (by hb_top_wp_simp) hlo hhi (Or.inl rfl)
    (Or.inr ⟨by bv_omega, by simp [unpack64_length]⟩) (fun _ => ?_)
    (hb_top_evalSvc_rt_sigaction hsvc (by hb_top_wp_simp))
  dsimp only []
  have htoBytes_emp : ({} : SigAction).toBytes = unpack64 0#64 ++ unpack64 0#64 ++ unpack64 0#64 ++ unpack64 0#64 := rfl
  wp_conv_pre =>
    dsimp only [kSigActionAt, optOldSigActionAt]
    simp only [State.writeReg64_sigActions, State.setPC_sigActions, State.setPState_sigActions,
      State.setMem_sigActions, State.getSigAction, hsig0', ho_f, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
    rw [htoBytes_emp, ← hb_top_fourCells_eq_bytes, ko1, ko2, ko3]
  conv => arg 3; simp only [beq_self_eq_true, ↓reduceIte]
  clear hf_23; wp_steps 11
  refine hb_step_bl_to (pc := b + 164#64) (dst := L.memcpyAddr) (by hb_top_wp_simp) (by hb_top_wp_simp) hf_41 ?_
  refine hb_step_cut fun s2 hs2 => ?_
  have ⟨hpc2, hrun2, hsp2, hsp_al2, hlr2, hx0_2, hx1_2, hx2_2, hx19_2⟩ :
      s2.pc = L.memcpyAddr ∧ s2.status = .Running ∧ s2.sp = s.sp - 112#64 ∧ s2.spAligned = true ∧
      s2.readReg64 .lr = L.libcSigactionAddr + 420#64 ∧ s2.readReg64 .x0 = oact + 8#64 ∧ s2.readReg64 .x1 = s.sp - 8#64 ∧
      s2.readReg64 .x2 = 8#64 ∧ s2.readReg64 .x19 = 0#64 := by
    rw [hs2]; refine ⟨by hb_top_wp_simp, by hb_top_wp_simp, by hb_top_wp_simp, ?_, by rw [← hb]; hb_top_wp_simp,
      by hb_top_wp_simp, by hb_top_wp_simp, by hb_top_wp_simp, by hb_top_wp_simp⟩
    simpa [State.spAligned, wp_norm, arm64_norm, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x70#64 hsp_align
  have hcs2 : CalleeSavedPreserved ((((s.writeReg64 .sp (s.sp - 112#64)).writeReg64 (.gpr 29#5) (s.sp - 112#64)).writeReg64 (.gpr 19#5) 0#64).writeReg64 (.gpr 20#5) oact |>.writeReg64 (.gpr 21#5) sig) s2 := by
    rw [hs2]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, bv_lin_norm]
  have hnv2 : HbNonVmFields s s2 := by rw [hs2]; hb_top_nv_rfl s
  clear hs2 hf_41 hpc hlr hx0 hx1 hx2 hsp_sub_al hsxtw
  refine step_hb_memcpy8 hmemcpy (ret_pc := L.libcSigactionAddr + 420#64) (dst := oact + 8#64) (src := s.sp - 8#64) (v := 0#64) (F := ?_)
    (fun R hm => by simp only [wp_norm, arm64_norm] at hm ⊢; revert hm; sep_frame)
    hpc2 hrun2 hlr2 hx0_2 hx1_2 hx2_2 fun s3 hpc3 hrun3 hsp3 hcs3 _ hnv23 => ?_
  have hsp3_eq : s3.sp = s.sp - 112#64 := hsp3.trans hsp2
  have hx19_3 : s3.readReg64 .x19 = 0#64 := hcs3.1.trans hx19_2
  have hpc3_b : s3.pc = b + 168#64 := by rw [hpc3, ← hb]; bv_lin
  clear hpc3; wp_steps 2
  refine hb_step_bl_to (pc := b + 116#64) (dst := L.syscallRetAddr) (by hb_top_wp_simp) (by simp [wp_norm, arm64_norm, hrun3]) hf_29 ?_
  refine hb_step_cut fun s3' hs3' => ?_
  have hsp3' : s3'.sp = s.sp - 112#64 := by rw [hs3']; simpa [wp_norm, arm64_norm] using hsp3_eq
  refine step_hb_top_syscallRet_zero hret' (ret_pc := b + 120#64) (F := ?_)
    (fun R hm => by rw [hsp3']; revert hm; sep_frame)
    (by rw [hs3']; hb_top_wp_simp) (by rw [hs3']; simp [wp_norm, arm64_norm, hrun3])
    (by rw [State.spAligned, hsp3']; simpa [State.spAligned, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x70#64 hsp_align)
    (by rw [hs3']; hb_top_wp_simp) (by rw [hs3']; hb_top_wp_simp)
    fun s4 hpc4 hrun4 hsp4 hsp_al4 hcs4_raw hx0_4 hnv4_raw => ?_
  have hcs4 : CalleeSavedPreserved s3 s4 := by rw [hs3'] at hcs4_raw; simpa [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] using hcs4_raw
  have hnv34 : HbNonVmFields s3 s4 := by rw [hs3'] at hnv4_raw; simpa [HbNonVmFields, wp_norm, arm64_norm] using hnv4_raw
  have hsp4_eq : s4.sp = s.sp - 112#64 := hsp4.trans hsp3'
  clear hs3' hsp4 hret' hf_29 hmemcpy
  have hsp_al4_raw : (s4.sp &&& 15#64 == 0#64) = true := hsp_al4
  have hsp_add_al : ((s4.sp + 112#64) &&& 15#64 == 0#64) = true := by simp only [beq_iff_eq] at hsp_al4_raw ⊢; bv_bits
  have e0 : s.sp - 112#64 = s4.sp := hsp4_eq.symm
  have e1 : s.sp - 104#64 = s4.sp + 8#64 := by rw [hsp4_eq]; bv_lin
  have e2 : s.sp - 96#64 = s4.sp + 16#64 := by rw [hsp4_eq]; bv_lin
  have e3 : s.sp - 88#64 = s4.sp + 24#64 := by rw [hsp4_eq]; bv_lin
  have e4 : s.sp - 80#64 = s4.sp + 32#64 := by rw [hsp4_eq]; bv_lin
  have hsp_end : s4.sp + 112#64 = s.sp := by rw [hsp4_eq]; bv_lin
  clear hsp4_eq; wp_conv_pre => rw [e0, e1, e2, e3, e4]
  wp_steps 4
  refine SepWP.weaken_pre_frame
    (P' := (((oact ↦₆₄ 0#64) ∗ ((oact + 8#64) ↦₆₄ 0#64) ∗ ((oact + 0x88#64) ↦₆₄ 0#64)) ∗ stackAt s.sp 0x90) ∗ G)
    (fun R hm => by
      simp only [State.mem_setPC, State.mem_writeReg64] at hm ⊢
      rw [← e4, ← e3, ← e2, ← e1, ← e0, hsp3'] at hm
      rw [pointsTo64_split32 (oact + 0x88#64) 0#64,
          show (0#64 : BitVec 64).extractLsb' 0 32 = 0#32 from rfl,
          show (0#64 : BitVec 64).extractLsb' 32 32 = 0#32 from rfl]
      rw [stackAt_split_cells s.sp 0x20 14 (by decide)]; fold_stack_cells) ?_
  refine hnext _ (by hb_top_wp_simp) (by simp [wp_norm, arm64_norm, hrun4]) (by hb_top_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_end] using hsp_align)
    (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] at hcs2 hcs3 hcs4 ⊢; simp [hcs2, hcs3, hcs4])
    (by simp [wp_norm, arm64_norm, hx0_4])
    (hnv2.trans (hnv23.trans (hnv34.trans (by hb_top_nv_rfl s4))))

end

private def HbLangStartGlobalsPre (C : HbCliLayout) (S : HbStartupLayout) : SepProp :=
  let L := C.std
  ((L.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗
  ((C.langStartVtableAddr + 0x28#64) ↦₆₄ᵣ C.langStartClosureAddr) ∗
  ((L.libcAddr + 1#64) ↦₈ 0#8) ∗ (S.eintrValidFlagAddr ↦₃₂ 0#32) ∗
  (C.needAltstackAddr ↦₈ 0#8) ∗ (S.mainThreadAddr ↦₆₄ 0#64) ∗
  (L.argcGlobalAddr ↦₆₄ 0#64) ∗ (L.argvGlobalAddr ↦₆₄ 0#64) ∗
  (S.threadInfoRootAddr ↦₆₄ 0#64) ∗ ((S.threadInfoRootAddr + 8#64) ↦₆₄ 0#64) ∗
  ((S.threadInfoRootAddr + 16#64) ↦₆₄ 0#64) ∗ (S.threadInfoLockAddr ↦₃₂ 0#32) ∗
  ((S.threadInfoLockAddr + 4#64) ↦₈ 0#8) ∗ ((S.threadInfoLockAddr + 8#64) ↦₆₄ 0#64) ∗
  (C.mainAltstackAddr ↦₆₄ 0#64) ∗ (L.pageSizeGlobalAddr ↦₆₄ 0#64) ∗
  (L.threadIdCounterAddr ↦₆₄ 0#64) ∗ (S.handlerSetAddr ↦₃₂ 0#32) ∗ (S.unmaskDoneAddr ↦₃₂ 0#32)

private def HbUserMainGlobalsPre (C : HbCliLayout) : SepProp :=
  let L := C.std
  hbRodata C.hbPl ∗ HbCliRoData C ∗
  (C.mallocng.roTablesAddr ↦ᵣ ProofLib.mallocngRoTablesBytes) ∗ MallocngInitialBss C.mallocng ∗
  ((L.stdoutGlobalAddr + 0x38#64) ↦₃₂ 3#32) ∗ (L.stdoutGlobalAddr ↦ₛ List.replicate 56 0#8) ∗
  HbStdinUninit C ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8)

private def HbPostMainGlobalsNoPs (C : HbCliLayout) (S : HbStartupLayout) : SepProp :=
  let L := C.std
  (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ (L.cleanupOnceAddr ↦₃₂ 3#32) ∗
  StdVtableRo L.cleanupVtableAddr L.cleanupVtableShimAddr L.cleanupClosureAddr ∗
  StdVtableRo L.stdoutVtableAddr L.stdoutVtableShimAddr L.stdoutCleanupClosureAddr ∗
  (L.exitingThreadIdAddr ↦₆₄ 0#64) ∗ HbMuslExitGlobalsNoNeedLocks C S 0#8

private def HbUnusedLoadSep (C : HbCliLayout) (S : HbStartupLayout) : SepProp :=
  let L := C.std
  (L.emptyCStrAddr ↦₈ᵣ 0#8) ∗ (L.devNullStdAddr ↦ᵣ devNullBytes) ∗
  (L.devNullLibcAddr ↦ᵣ devNullBytes) ∗ HbLangStartVtableRo C ∗
  ((L.stdoutGlobalAddr + 0x3c#64) ↦₃₂ 0#32) ∗ ((L.libcAddr + 2#64) ↦₈ 0#8) ∗
  ((L.libcAddr + 4#64) ↦₃₂ 0#32) ∗ ((L.libcAddr + 0x38#64) ↦ₛ List.replicate 48 0#8) ∗
  (L.threadListLockAddr ↦₃₂ 0#32) ∗ ((S.handlerSetAddr + 4#64) ↦₃₂ 0#32)

private theorem hbCliRoData_dup_panicCount (C : HbCliLayout) :
    HbCliRoData C = HbCliRoData C ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) := by
  conv => lhs; unfold HbCliRoData; rw [← pointsTo64RO_dup C.globalPanicCountAddr 0#64]
  unfold HbCliRoData; ac_rfl

private theorem hbLangStartVtableRo_dup_closure (C : HbCliLayout) :
    HbLangStartVtableRo C =
      HbLangStartVtableRo C ∗ ((C.langStartVtableAddr + 0x28#64) ↦₆₄ᵣ C.langStartClosureAddr) := by
  conv => lhs; unfold HbLangStartVtableRo; dsimp only; rw [← pointsTo64RO_dup (C.langStartVtableAddr + 0x28#64) C.langStartClosureAddr]
  unfold HbLangStartVtableRo; dsimp only; ac_rfl

set_option maxHeartbeats 400000 in
private theorem hbLoad_to_cMain {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (cPre : HbPreMainCode P C S) (hS : S.Valid C) (hm : HbMatchesImage C S img = true)
    (hvalid : inputs.Valid) (hload : img.loadState inputs = .ok s0)
    (hrx : C.std.rxProgram img = P) :
    let sl := StackLayout.of img inputs
    let haveLse : BitVec 8 := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8
    ∃ s_cm : State,
      InitialStackInfo img inputs s0 ∧
      P.CodeLoaded s0.mem ∧
      Steps P s0 s_cm ∧
      s_cm.pc = C.std.cMainAddr ∧
      s_cm.status = .Running ∧
      s_cm.sp = sl.sp0 - 0x30#64 ∧
      s_cm.spAligned = true ∧
      s_cm.readReg64 .x30 = C.std.libcStartMainStage2Addr + 0x38#64 ∧
      s_cm.readReg64 .x0 = BitVec.ofNat 64 inputs.argv.length ∧
      s_cm.readReg64 .x1 = sl.argvTableAddr ∧
      s_cm.tpidrEl0 = C.std.builtinTlsAddr + 0xc8#64 ∧ s_cm.sigAltStack = {} ∧
      StdTlsFieldsPreserved s0 s_cm ∧
      (s_cm.mem ⊨
        stackAt sl.sp0 48 ∗ memRegion (sl.sp0 - 524288#64) 523408 ∗ stackAt (sl.sp0 - 0x30#64) 0x340 ∗
        (C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
        ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗
        (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗
        (((C.std.builtinTlsAddr + 0xc8#64) - 0xa4#64) ↦₃₂ 0#32) ∗
        (((C.std.builtinTlsAddr + 0xc8#64) + 0x58#64) ↦₆₄ 0#64) ∗
        HbLangStartGlobalsPre C S ∗ HbUserMainGlobalsPre C ∗ HbPostMainGlobalsNoPs C S ∗
        ∃∗ R_st12 : SepProp, R_st12) := by
  dsimp only
  let sl := StackLayout.of img inputs
  let haveLse : BitVec 8 := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8
  obtain ⟨hinfo, hcode0, hsat0⟩ := hbLoadState_initial hS hm hvalid hload
  rw [hrx] at hcode0
  let F_st12 : SepProp :=
    memRegion (sl.sp0 - 524288#64) 523744 ∗ ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗
    (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗ (sl.platformAddr ↦ᵣ platformCStringBytes) ∗
    HbLangStartGlobalsPre C S ∗ HbUserMainGlobalsPre C ∗ HbPostMainGlobalsNoPs C S ∗
    HbUnusedLoadSep C S
  have hpre_s0 : s0.mem ⊨
      ((memRegion (sl.sp0 - 0x1c0#64) 0x1c0 ∗ Stage1GlobalsPre C.std ∗ HbStage1Got C S ∗
        HbStage2GlobalsPre C S ∗
        (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗ (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
        (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗ (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        (sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ HbPreTlsSep C.std sl.sp0) ∗ F_st12) ∗ emp := by
    rw [sepConj_emp]
    refine Satisfies.mono ?_ hsat0
    unfold HbStartupRoAll StdRoConstants HbRelroRwGlobals hbRelroRwAtoms StdDataGlobals
      StdBinaryLayout.dataNoStderrAtoms StdLibcGlobals StdBinaryLayout.libcAtoms
      HbExtraRwGlobals hbExtraRwAtoms HbInitialStackSep
    dsimp only [rwAtomListSep, RwAtom.toSepProp]
    rw [hbStack_s0_split sl.sp0, hbLangStartVtableRo_dup_closure C, hbCliRoData_dup_panicCount C,
        pointsTo64_split32 S.handlerSetAddr 0#64,
        show (0#64 : BitVec 64).extractLsb' 0 32 = 0#32 from rfl,
        show (0#64 : BitVec 64).extractLsb' 32 32 = 0#32 from rfl]
    dsimp only [Stage1GlobalsPre, HbStage1Got, HbStage2GlobalsPre, HbPreTlsSep, StdLibcTlsZero,
      F_st12, HbLangStartGlobalsPre, HbUserMainGlobalsPre, HbStdinUninit, HbPostMainGlobalsNoPs,
      HbMuslExitGlobalsNoNeedLocks, HbUnusedLoadSep]
    sep_entail
  obtain ⟨s_cm, hsteps, hres | ⟨_, hfalse⟩⟩ :=
    SepWP.to_reaches_pc (hbStage12_to_cMain (F := F_st12) hS hm hvalid hinfo cPre) hpre_s0 hcode0
  · obtain ⟨hpc, hrun, P_cm, hm_cm, ⟨hsp, hsp_al, hlr, hx0, hx1, _, htp, hsas_cm, htls⟩, hent_cm⟩ := hres
    rw [sepConj_emp] at hm_cm
    have hm_cm' := Satisfies.mono hent_cm hm_cm
    refine ⟨s_cm, hinfo, hcode0, hsteps, hpc, hrun, hsp, hsp_al, hlr, hx0, hx1, htp,
      hsas_cm.trans hinfo.s0_sigAltStack, htls, ?_⟩
    refine Satisfies.mono ?_ hm_cm'
    dsimp only [Stage1GlobalsPost, HbStage2GlobalsPost, F_st12]
    refine Entails.trans (Q := (memRegion (sl.sp0 - 524288#64) 523744 ∗ memRegion (sl.sp0 - 0x220#64) 0x1f0) ∗
      (stackAt sl.sp0 48 ∗ (C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗
       ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
       ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
       ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗
       (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
       (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗
       (((C.std.builtinTlsAddr + 0xc8#64) - 0xa4#64) ↦₃₂ 0#32) ∗
       (((C.std.builtinTlsAddr + 0xc8#64) + 0x58#64) ↦₆₄ 0#64) ∗
       HbLangStartGlobalsPre C S ∗ HbUserMainGlobalsPre C ∗ HbPostMainGlobalsNoPs C S) ∗ ?R_dead)
      (by sep_frame) ?_
    rw [hbStack_cm_split sl.sp0]
    refine Entails.trans (Q := stackAt sl.sp0 48 ∗
      memRegion (sl.sp0 - 524288#64) 523408 ∗ stackAt (sl.sp0 - 0x30#64) 0x340 ∗
      (C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗
      ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
      ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
      ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗
      (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
      (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗
      (((C.std.builtinTlsAddr + 0xc8#64) - 0xa4#64) ↦₃₂ 0#32) ∗
      (((C.std.builtinTlsAddr + 0xc8#64) + 0x58#64) ↦₆₄ 0#64) ∗
      HbLangStartGlobalsPre C S ∗ HbUserMainGlobalsPre C ∗ HbPostMainGlobalsNoPs C S ∗ ?R_dead)
      (by sep_entail)
      (by
        iterate 14 apply sepConj_mono_right
        exact Entails.sepExists_right _ (Entails.refl _))
  · exact False.elim (not_satisfies_false_sepConj hfalse)

private theorem hbSignalHandler_gt1 {C : HbCliLayout} {S : HbStartupLayout} {img : ElfImage}
    (hm : HbMatchesImage C S img = true) :
    1 < S.signalHandlerAddr.toNat := by
  obtain ⟨hwf, _, _, _, _, _, _, roSeg, rxSeg, relroSeg, rwSeg, _, hrx, _, _, _, hcode, _, _, _⟩ :=
    HbMatchesImage.unpack hm
  have hmem : S.signalHandlerAddr ∈ hbAllCodeAddrs C S := by simp [hbAllCodeAddrs]
  have hall := List.all_eq_true.mp hcode S.signalHandlerAddr hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  have ⟨_, _, hseg⟩ := wellFormed_segments_bounds hwf
  have hrx_mem := List.mem_of_getElem? hrx
  have hrx_lo := (hseg.2.2 rxSeg hrx_mem).1
  omega

private theorem hbAuxv_minsigstksz_le {img : ElfImage} {inputs : ProcessInputs}
    (hvalid : inputs.Valid) (platformAddr randomAddr execfnAddr : BitVec 64) :
    ∀ e ∈ mkAuxvEntries img inputs platformAddr randomAddr execfnAddr,
      e.1 = 51#64 → e.2.toNat ≤ 524288 := by
  rintro ⟨t, v⟩ hmem ht
  subst ht
  unfold mkAuxvEntries at hmem
  rw [List.mem_append] at hmem
  rcases hmem with hfix | hext
  · simp [mkFixedAuxvEntries, AuxvTag.phdr, AuxvTag.phent, AuxvTag.phnum, AuxvTag.pagesz,
      AuxvTag.base, AuxvTag.flags, AuxvTag.entry, AuxvTag.uid, AuxvTag.euid, AuxvTag.gid,
      AuxvTag.egid, AuxvTag.clktck, AuxvTag.platform, AuxvTag.hwcap, AuxvTag.secure,
      AuxvTag.random, AuxvTag.hwcap2, AuxvTag.execfn] at hfix
  · exact hvalid.auxv.minsigstksz_bound (51#64, v) hext rfl

private theorem hbCanMap_brkGap {addrs : ProofLib.MallocngAddrs} {stackBase stackTop len : Nat} {s0 s : State}
    (hmwf : MallocngInitialMemWf addrs 4096 stackBase stackTop s0)
    (hbrk_hi : addrs.brkBase.toNat ≤ 5 * 2 ^ 20)
    (hlen_hi : len ≤ 528384)
    (hperm : ∀ a, s.mem.perm a = s0.mem.perm a) :
    s.mem.canMap addrs.brkBase len = true := by
  unfold Memory.canMap
  rw [Memory.allPerm_iff]
  intro i hi
  rw [hperm]
  rcases hmwf with ⟨_, _, _, _, _, _, hstk_min, _, _, _, hmap0⟩
  unfold STACK_BASE_MIN at hstk_min
  have ha_nat : (addrs.brkBase + BitVec.ofNat 64 i).toNat = addrs.brkBase.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  cases hmp : (s0.mem.perm (addrs.brkBase + BitVec.ofNat 64 i)).mapped
  · rfl
  · exfalso
    rcases hmap0 _ hmp with ⟨_, hlt⟩ | ⟨hge, _⟩ <;> omega

private theorem hbMapped_inIntervals {addrs : ProofLib.MallocngAddrs} {stackBase stackTop altLen : Nat}
    {altBase : BitVec 64} {s0 s_cm s_main : State}
    (hmwf : MallocngInitialMemWf addrs 4096 stackBase stackTop s0)
    (halt4k : 4096 ≤ altLen)
    (hperm_cm : ∀ a, s_cm.mem.perm a = s0.mem.perm a)
    (hperm_m : ∀ a, s_main.mem.perm a =
      ((s_cm.mem.mapZero altBase altLen).setPermNonFrozen altBase 4096 Perm.protNone).perm a) :
    ∀ a : BitVec 64, (s_main.mem.perm a).mapped = true →
      MallocngInIntervals
        [(0#64, addrs.brkBase.toNat),
         (BitVec.ofNat 64 stackBase, stackTop - stackBase),
         (altBase, altLen)] a := by
  intro a ha
  rw [hperm_m a, Memory.perm_setPermNonFrozen, Memory.perm_mapZero] at ha
  rcases hmwf with ⟨_, _, _, _, _, _, _, hstk_le, _, hstk_top, hmap0⟩
  unfold TASK_SIZE at hstk_top
  by_cases halt : (a - altBase).toNat < altLen
  · exact ⟨(altBase, altLen), by simp, halt⟩
  · have h4k : ¬ ((a - altBase).toNat < 4096) := by omega
    simp only [decide_eq_false halt, decide_eq_false h4k, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hperm_cm a] at ha
    rcases hmap0 a ha with ⟨_, hlt⟩ | ⟨hge, hlt⟩
    · exact ⟨(0#64, addrs.brkBase.toNat), by simp, by simpa using hlt⟩
    · refine ⟨(BitVec.ofNat 64 stackBase, stackTop - stackBase), by simp, ?_⟩
      have hsb : (BitVec.ofNat 64 stackBase).toNat = stackBase := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hsb]; exact hge)), hsb]
      omega

private theorem hb_isAligned_w32_of_mod4 {a : BitVec 64} (h : a.toNat % 4 = 0) :
    MemWidth.isAligned .W32 a = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]; change a.toNat &&& 3 = 0
  rw [Nat.and_two_pow_sub_one_eq_mod _ 2]; exact h

private theorem hb_isAligned_x64_of_mod8 {a : BitVec 64} (h : a.toNat % 8 = 0) :
    MemWidth.isAligned .X64 a = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]; change a.toNat &&& 7 = 0
  rw [Nat.and_two_pow_sub_one_eq_mod _ 3]; exact h

private theorem hasCode_withSvc {P : Program} {svc : State → State} {a : BitVec 64} {ws : List (BitVec 32)}
    (h : P.hasCode a ws) : (P.withSvc svc).hasCode a ws := by
  cases P; exact h

private theorem hb_hasInstrs_withSvc {P : Program} {svc : State → State} {base : BitVec 64} {is : List Instr}
    (h : hasInstrs P base is) : hasInstrs (P.withSvc svc) base is := by
  intro i hi; rw [Program.withSvc_fetch]; exact h i hi

set_option maxHeartbeats 400000 in
private theorem hbStep_cMain_to_userMain {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {img : ElfImage} {inputs : ProcessInputs} {s0 s_cm : State} {R_cm : SepProp}
    (cPre : HbPreMainCode P C S) (hv : C.Valid) (hS : S.Valid C)
    (hm : HbMatchesImage C S img = true) (hvalid : inputs.Valid)
    (hbudget : HashbrownStdinBudget inputs)
    (hinfo : InitialStackInfo img inputs s0) (hcode_cm : P.CodeLoaded s_cm.mem)
    (hpc : s_cm.pc = C.std.cMainAddr) (hrun : s_cm.status = .Running)
    (hsp : s_cm.sp = (StackLayout.of img inputs).sp0 - 0x30#64) (hsp_al : s_cm.spAligned = true)
    (hlr : s_cm.readReg64 .x30 = C.std.libcStartMainStage2Addr + 0x38#64)
    (hx0 : s_cm.readReg64 .x0 = BitVec.ofNat 64 inputs.argv.length)
    (hx1 : s_cm.readReg64 .x1 = (StackLayout.of img inputs).argvTableAddr)
    (htp : s_cm.tpidrEl0 = C.std.builtinTlsAddr + 0xc8#64)
    (htls : StdTlsFieldsPreserved s0 s_cm)
    (hsas_cm : s_cm.sigAltStack = {})
    (hsat_cm : s_cm.mem ⊨
      (stackAt (StackLayout.of img inputs).sp0 48 ∗
        stackAt ((StackLayout.of img inputs).sp0 - 0x30#64) 0x340 ∗
        (C.std.haveLseAtomicsAddr ↦₈ (if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8)) ∗
        ((C.std.libcAddr + 0x08#64) ↦₆₄ (StackLayout.of img inputs).auxvTableAddr) ∗
        ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
        ((StackLayout.of img inputs).auxvTableAddr ↦ₛ encodeAuxvBytes (StackLayout.of img inputs).auxvEntries) ∗
        (((C.std.builtinTlsAddr + 0xc8#64) - 0xa4#64) ↦₃₂ 0#32) ∗
        (((C.std.builtinTlsAddr + 0xc8#64) + 0x58#64) ↦₆₄ 0#64) ∗ HbLangStartGlobalsPre C S) ∗ R_cm) :
    let sl := StackLayout.of img inputs
    let tp := C.std.builtinTlsAddr + 0xc8#64
    let haveLse : BitVec 8 := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8
    ∃ (s_main : State) (altBase : BitVec 64) (e0 : BitVec 32),
      Steps P s_cm s_main ∧ 4096 ≤ altBase.toNat ∧ altBase.toNat % 4096 = 0 ∧
      altBase.toNat + (hbExpectedAltRawSz sl.auxvEntries + 4096) ≤ 2 ^ 48 ∧
      s_cm.mem.canMap altBase (hbExpectedAltRawSz sl.auxvEntries + 4096) = true ∧
      s_main.pc = C.std.userMainAddr ∧ s_main.status = .Running ∧
      s_main.sp = sl.sp0 - 0x170#64 ∧ s_main.spAligned = true ∧
      s_main.readReg64 .lr = C.std.beginShortBacktraceAddr + 0x0c#64 ∧
      s_main.tpidrEl0 = tp ∧ s_main.fs = initFsState inputs ∧ s_main.trace = [] ∧
      s_main.physMemAvail = inputs.init.physMemAvail - (hbExpectedAltRawSz sl.auxvEntries + 4096) ∧
      s_main.brk = C.mallocng.brkBase ∧ s_main.brkStart = C.mallocng.brkBase ∧
      (∀ a, s_main.mem.perm a =
        ((s_cm.mem.mapZero altBase (hbExpectedAltRawSz sl.auxvEntries + 4096)).setPermNonFrozen altBase 4096 Perm.protNone).perm a) ∧
      (s_main.mem ⊨ ((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ HbThreadIdInv C tp ∗
        ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
        (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗ ((tp - 0xa4#64) ↦₃₂ e0) ∗
        (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
        HbAltstackInv4k C S (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
        HbAltstackMappedPre (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
        HbCallerFrames C sl.sp0 ∗ stackAt (sl.sp0 - 0x170#64) 0x200 ∗ ∃∗ R_ls : SepProp, R_ls) ∗ R_cm) := by
  dsimp only; let sl := StackLayout.of img inputs; let tp := C.std.builtinTlsAddr + 0xc8#64
  let haveLse : BitVec 8 := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8
  obtain ⟨hwf, _, _, _, hbrk_eq, ⟨hbrk_lo, hbrk_hi⟩, _, _⟩ := HbMatchesImage.unpack hm
  have hbrk_base_nat : C.mallocng.brkBase.toNat = img.brkStart.toNat :=
    congrArg BitVec.toNat (hv.brkBase_eq.trans hbrk_eq.symm)
  have hbrk_img_nat : img.brkStart.toNat = C.std.brkStart.toNat := congrArg BitVec.toNat hbrk_eq
  have hbrk_ge64k : 65536 ≤ C.mallocng.brkBase.toNat := by omega
  have hbrk_le5m : C.mallocng.brkBase.toNat ≤ 5 * 2 ^ 20 := by omega
  have hsize_le : inputs.init.stackSize ≤ inputs.init.stackTop.toNat := by
    have hfl := hinfo.stackBase_floor; unfold STACK_BASE_MIN at hfl; omega
  have hstackCeil : inputs.init.stackSize ≤ 128 * 2 ^ 20 := by
    have hle := hvalid.stackSize_le; unfold STACK_SIZE_MAX at hle; omega
  have hmwf0 := hinfo.mallocngInitialMemWf (hv.brkBase_eq.trans hbrk_eq.symm)
    (by omega) (by omega) hsize_le hstackCeil hwf
  have hbrk_al4k : C.mallocng.brkBase.toNat % 4096 = 0 := hmwf0.2.2.1
  have hsp0_lo : 2 ^ 38 ≤ sl.sp0.toNat := by
    have hfl := hinfo.stackBase_floor; unfold STACK_BASE_MIN at hfl
    have hhr := hinfo.sp0_headroom.2; change _ ≤ sl.sp0.toNat at hhr; omega
  have htop48 : inputs.init.stackTop.toNat ≤ 2 ^ 48 := hinfo.stackTop_align.2.2
  have han := hinfo.addrs_nat; dsimp only at han
  obtain ⟨h1, _, h3, h4, h5, h6, _, _, h9⟩ := han
  have hsp0_hi : sl.sp0.toNat ≤ 2 ^ 48 := by dsimp only [sl]; omega
  have hsp_sub150_lo : 0x220 ≤ sl.sp0.toNat - 0x150 :=
    Nat.le_sub_of_add_le (Nat.le_trans (by decide) hsp0_lo)
  have hsp_sub150_fit24 : (sl.sp0.toNat - 0x150) + 24 ≤ 2 ^ 64 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.le_trans (Nat.sub_le _ _) hsp0_hi) 24) (by decide)
  have hsp_sub150_80_lo : 0x90 ≤ sl.sp0.toNat - 0x150 - 80 :=
    Nat.le_sub_of_add_le (Nat.le_trans (by decide) hsp_sub150_lo)
  have hsp_sub150_ne0 : sl.sp0.toNat - 0x150 ≠ 0 :=
    Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hsp_sub150_lo)
  have hsp_sub150_nat : (s_cm.sp - 0x120#64).toNat = sl.sp0.toNat - 0x150 := by
    rw [hsp, show sl.sp0 - 0x30#64 - 0x120#64 = sl.sp0 - 0x150#64 by bv_lin,
        BitVec.toNat_sub_of_le (BitVec.le_def.mpr (Nat.le_trans (by decide) hsp0_lo))]
    rfl
  have hbnd : ∀ e ∈ sl.auxvEntries, e.1 = 51#64 → e.2.toNat ≤ 524288 := by
    dsimp only [sl]; rw [hinfo.auxvEntries_eq]
    exact hbAuxv_minsigstksz_le hvalid sl.platformAddr sl.randomAddr sl.execfnAddr
  have ⟨_, hrawLo, hrawHi⟩ := hbExpectedAltRawSz_spec hbnd
  have halt_sz_le : hbExpectedAltRawSz sl.auxvEntries + 4096 ≤ 528384 :=
    Nat.add_le_add_right hrawHi 4096
  have hbrk_alt_fit : C.mallocng.brkBase.toNat + (hbExpectedAltRawSz sl.auxvEntries + 4096) ≤ 2 ^ 48 :=
    Nat.le_trans (Nat.add_le_add hbrk_le5m halt_sz_le) (by decide)
  have hwf_aux := mkAuxvEntries_wf img hvalid.auxv sl.platformAddr sl.randomAddr sl.execfnAddr
  rw [← hinfo.auxvEntries_eq] at hwf_aux
  obtain ⟨_, _, hnonull_aux⟩ := hwf_aux
  have hsig_gt1 := hbSignalHandler_gt1 hm
  have hal_tid : MemWidth.isAligned .X64 C.std.threadIdCounterAddr = true :=
    hb_isAligned_x64_of_mod8 hv.threadIdCtr_align
  have hal_hs : MemWidth.isAligned .W32 S.handlerSetAddr = true :=
    hb_isAligned_w32_of_mod4 (by have := hS.handlerSet_align; omega)
  have hal_errno : MemWidth.isAligned .W32 (tp - 0xa4#64) = true := by
    apply hb_isAligned_w32_of_mod4
    have hbt := hS.builtinTls_align; have hlo := hS.builtinTls_lo; have hhi := hS.builtinTls_noWrap
    have htp_nat : (tp - 0xa4#64).toNat = C.std.builtinTlsAddr.toNat + 0x24 := by
      dsimp only [tp]
      rw [show C.std.builtinTlsAddr + 0xc8#64 - 0xa4#64 = C.std.builtinTlsAddr + 0x24#64 by bv_lin,
          BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rcases cPre.sigSys with
    ⟨hsccp, hcp, hret, hpoll_c, hsig_c, hsig_fast, hlsa_head, hlsa_mid, hlsa_tail,
     hsysconf_c, hsysconf_epi, hsas_c, hmmap_c, hmprot_c⟩
  rcases cPre.makeHandler with ⟨hmh_head, hmh_body⟩
  obtain ⟨_, _, _, _, _, hc_getaux, hc_errno, _⟩ := cPre.stage2
  let Pmh_in : SepProp :=
    ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
    (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
    ((tp - 0xa4#64) ↦₃₂ 0#32)
  let Pmh_out : BitVec 64 → SepProp := fun altBase =>
    memMapped altBase (4096 + hbExpectedAltRawSz sl.auxvEntries) ∗
    ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
    (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
    (∃∗ e1 : BitVec 32, (tp - 0xa4#64) ↦₃₂ e1)
  let Pin11 : SepProp :=
    ((C.std.libcAddr + 1#64) ↦₈ 0#8) ∗ (S.handlerSetAddr ↦₃₂ 0#32) ∗
    (S.unmaskDoneAddr ↦₃₂ 0#32) ∗ (S.eintrValidFlagAddr ↦₃₂ 0#32)
  let Pcustom11 : SepProp :=
    ((C.std.libcAddr + 1#64) ↦₈ 0#8) ∗ (S.handlerSetAddr ↦₃₂ 0x400#32) ∗
    (S.unmaskDoneAddr ↦₃₂ 1#32) ∗ (S.eintrValidFlagAddr ↦₃₂ 1#32)
  let Pcustom7 : SepProp :=
    ((C.std.libcAddr + 1#64) ↦₈ 0#8) ∗ (S.handlerSetAddr ↦₃₂ 0x440#32) ∗
    (S.unmaskDoneAddr ↦₃₂ 1#32) ∗ (S.eintrValidFlagAddr ↦₃₂ 1#32)
  have hwp : SepWP P C.std.userMainAddr s_cm
      (stackAt sl.sp0 48 ∗ stackAt (sl.sp0 - 0x30#64) 0x340 ∗
        (C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗
        ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
        ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
        (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        ((tp - 0xa4#64) ↦₃₂ 0#32) ∗ ((tp + 0x58#64) ↦₆₄ 0#64) ∗ HbLangStartGlobalsPre C S)
      (fun sf Pf => ∃ (altBase : BitVec 64) (e0 : BitVec 32),
        4096 ≤ altBase.toNat ∧ altBase.toNat % 4096 = 0 ∧
        altBase.toNat + (hbExpectedAltRawSz sl.auxvEntries + 4096) ≤ 2 ^ 48 ∧
        s_cm.mem.canMap altBase (hbExpectedAltRawSz sl.auxvEntries + 4096) = true ∧
        sf.sp = sl.sp0 - 0x170#64 ∧ sf.spAligned = true ∧
        sf.readReg64 .lr = C.std.beginShortBacktraceAddr + 0x0c#64 ∧
        sf.tpidrEl0 = tp ∧ sf.fs = initFsState inputs ∧ sf.trace = [] ∧
        sf.physMemAvail = inputs.init.physMemAvail - (hbExpectedAltRawSz sl.auxvEntries + 4096) ∧
        sf.brk = C.mallocng.brkBase ∧ sf.brkStart = C.mallocng.brkBase ∧
        (∀ a, sf.mem.perm a =
          ((s_cm.mem.mapZero altBase (hbExpectedAltRawSz sl.auxvEntries + 4096)).setPermNonFrozen altBase 4096 Perm.protNone).perm a) ∧
        (Pf ⊢ (C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ HbThreadIdInv C tp ∗
          ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
          ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
          (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
          ((tp - 0xa4#64) ↦₃₂ e0) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
          HbAltstackInv4k C S (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
          HbAltstackMappedPre (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
          HbCallerFrames C sl.sp0 ∗ stackAt (sl.sp0 - 0x170#64) 0x200 ∗
          ∃∗ R_ls : SepProp, R_ls)) := by
    refine hbCMain_to_userMain (Pmh_in := Pmh_in) (Pmh_out := Pmh_out)
      (Pin11 := Pin11) (Pcustom11 := Pcustom11) (Pcustom7 := Pcustom7)
      (v_mt := 0#64) (v_ps := 0#64) (v_ma := 0#64) (v_argc := 0#64) (v_argv := 0#64)
      (F := emp) cPre hS.argv_eq hinfo.argc_bounds.2.1 hbnd
      (fun R hm => by dsimp only [HbLangStartGlobalsPre, Pmh_in, Pin11, tp] at hm ⊢; revert hm; sep_frame)
      hpc hrun hsp hsp_al hlr hx0 hx1 htp
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro s0' G hpc0 hrun0 _ _ hlr0 hx0_0 hx1_0 hx2_0 hk
      refine SepWP.weaken_pre_frame (fun _ hm => by revert hm; sep_frame)
        (step_hb_cas8Relax_rw (hb_hasInstrs_withSvc cPre.cas8Relax) hpc0 hrun0 hx0_0 hx1_0 hx2_0 hal_tid
          fun s1 hpc1 hrun1 hsp1 hx0_1 hcs1 hnv1 => ?_)
      refine SepWP.weaken_pre_frame (fun _ hm => by simp only [beq_self_eq_true, ↓reduceIte] at hm; revert hm; sep_frame)
        (hk s1 (hlr0 ▸ hpc1) hrun1 hsp1 hcs1 hx0_1 hnv1)
    · intro s0' G hpc0 hrun0 hsp0 hal0 hlr0 hx0_0 hx1_0 hx2_0 hfs0 hk
      have hsp0_lo' : 0x40 ≤ s0'.sp.toNat := by
        rw [hsp0, hsp_sub150_nat]; exact Nat.le_trans (by decide) hsp_sub150_lo
      have hfit0 : s0'.sp.toNat + 24 ≤ 2 ^ 64 := by
        rw [hsp0, hsp_sub150_nat]; exact hsp_sub150_fit24
      have heval0 : evalPpollBytes s0'.fs stdioPollfdBytes 0 = some (stdioPollfdBytes, 0) := by
        rw [hfs0, htls.1, hinfo.s0_fs]; exact evalPpollBytes_initFsState inputs
      exact step_hb_poll_stdio3 (Or.inr rfl) (hasCode_withSvc hsccp) (hb_hasInstrs_withSvc hcp)
        (hasCode_withSvc hret) (hb_hasInstrs_withSvc hpoll_c) (fun _ hm => by revert hm; sep_frame)
        hpc0 hrun0 hal0 hsp0_lo' hlr0 hx0_0 hx1_0 (by simp [State.readReg32, hx2_0]) hfit0 heval0 hk
    · intro s0' G hpc0 hrun0 hsp0 hal0 hlr0 hx0_0 hx1_0 hnv0 hk
      have hsp0_lo' : 0x220 ≤ s0'.sp.toNat := by
        rw [hsp0, hsp_sub150_nat]; exact hsp_sub150_lo
      have hsig0 : s0'.getSigAction 13#32 = {} := by
        rw [State.getSigAction, hnv0.2.2.2.1, htls.2.2.1, hinfo.s0_sigActions]
      exact step_hb_signal_sigpipe_ign (Or.inr rfl) (hb_hasInstrs_withSvc hsig_c) (hb_hasInstrs_withSvc hsig_fast)
        (hasCode_withSvc hlsa_head) (hb_hasInstrs_withSvc hlsa_tail) (hasCode_withSvc hret)
        (hb_hasInstrs_withSvc cPre.memOps.memcpy) (fun _ hm => by revert hm; sep_frame)
        hpc0 hrun0 hal0 hsp0_lo' hlr0 hx0_0 hx1_0 hsig0 hk
    · intro s0' G hpc0 hrun0 _ hal0 hlr0 hx0_0 hk
      exact step_hb_sysconf_pagesize (hb_hasInstrs_withSvc hsysconf_c) (hasCode_withSvc hsysconf_epi)
        (fun _ hm => by revert hm; sep_frame) hpc0 hrun0 hal0 hlr0 hx0_0 hk
    · intro s0' G hpc0 hrun0 hsp0 hal0 hlr0 hx0_0 hx1_0 hx2_0 hnv0 hk
      refine step_hb_sigaction_wrap (hb_hasInstrs_withSvc hsig_fast) (actOpt := none)
        (Pin := (s0'.sp ↦₆₄ 0#64) ∗ ((s0'.sp + 8#64) ↦₆₄ 0#64) ∗ ((s0'.sp + 0x88#64) ↦₆₄ 0#64))
        (Pout := fun _ => (s0'.sp ↦₆₄ 0#64) ∗ ((s0'.sp + 8#64) ↦₆₄ 0#64) ∗ ((s0'.sp + 0x88#64) ↦₆₄ 0#64)) (F := G)
        (fun _ hm => by rw [sepConj_assoc] at hm; exact hm) hpc0 hrun0 hal0 hlr0 hx0_0 hx1_0 hx2_0 (Or.inr (Or.inl rfl))
        (fun si Gi hpci hruni hspi hali hlri hx0i hx1i hx2i hnvi hki => ?_)
        (fun sf _ hpcf hrunf hspf half hcsf hx0f hnvf => hk sf hpcf hrunf hspf half hcsf hx0f hnvf)
      have hspi_lo : 0x90 ≤ si.sp.toNat := by
        rw [hspi, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hsp0, hsp_sub150_nat]; exact Nat.le_trans (by decide) hsp_sub150_lo)),
            hsp0, hsp_sub150_nat]; exact hsp_sub150_80_lo
      have hoact_ne : s0'.sp ≠ 0#64 := fun heq => by
        have h0 := congrArg BitVec.toNat heq; rw [hsp0, hsp_sub150_nat] at h0
        exact hsp_sub150_ne0 h0
      have hsig11 : si.getSigAction 11#32 = {} := by
        rw [State.getSigAction, hnvi.2.2.2.1, hnv0.2.2.2.1]
        simp [State.setSigAction, htls.2.2.1, hinfo.s0_sigActions]
      exact step_hb_libcSigaction_probe_zero (Or.inr rfl) (hasCode_withSvc hlsa_head) (hb_hasInstrs_withSvc hlsa_tail)
        (hasCode_withSvc hret) (hb_hasInstrs_withSvc cPre.memOps.memcpy) hpci hruni hali hspi_lo hlri hx0i hx1i hx2i
        (Or.inl rfl) hoact_ne hsig11 rfl fun s1 hpc1 hrun1 hsp1 hal1 hcs1 hx0_1 hnv1 => hki s1 0#64 hpc1 hrun1 hsp1 hal1 hcs1 hx0_1 hnv1
    · intro s_mh G hpc_mh hrun_mh hsp_mh hal_mh hlr_mh hx0_mh hnv_mh hvm_mh hk
      have hsp_mh_lo : 0xd0 ≤ s_mh.sp.toNat := by
        rw [hsp_mh, hsp_sub150_nat]; exact Nat.le_trans (by decide) hsp_sub150_lo
      have hsas_mh : s_mh.sigAltStack = {} := hnv_mh.2.2.2.2.trans hsas_cm
      have htp_mh : s_mh.tpidrEl0 = tp := hnv_mh.2.2.1.trans htp
      have hphys_mh : hbExpectedAltRawSz sl.auxvEntries + 4096 ≤ s_mh.physMemAvail := by
        rw [hvm_mh.physMemAvail_eq, htls.2.2.2.2.2.1, hinfo.s0_physMemAvail]
        exact Nat.le_trans halt_sz_le (Nat.le_trans (by decide : 528384 ≤ 8 * 2 ^ 20)
          (Nat.le_trans (Nat.le_add_right _ _) hbudget.2))
      have hgap_mh : ∃ gap : BitVec 64, 65536 ≤ gap.toNat ∧ gap.toNat % 4096 = 0 ∧
          gap.toNat + (hbExpectedAltRawSz sl.auxvEntries + 4096) ≤ 2 ^ 48 ∧
          s_mh.mem.canMap gap (hbExpectedAltRawSz sl.auxvEntries + 4096) = true :=
        ⟨C.mallocng.brkBase, hbrk_ge64k, hbrk_al4k, hbrk_alt_fit,
         hbCanMap_brkGap hmwf0 hbrk_le5m halt_sz_le
           (fun a => (hvm_mh.perm_eq a).trans (htls.2.2.2.2.2.2 a))⟩
      refine step_hb_make_handler cPre.no_hooks cPre.svc_eq hmh_head hmh_body hsas_c hc_getaux hc_errno hmmap_c hmprot_c hret
        (errno0 := 0#32)
        (fun R hm => by
          dsimp only [Pmh_in, muslErrnoAddr] at hm ⊢
          rw [htp_mh]
          rw [← hsp_mh, stackAt_split_bottom s_mh.sp 0xd0 336 (by decide)] at hm
          revert hm; sep_frame)
        hpc_mh hrun_mh hal_mh hsp_mh_lo hlr_mh hx0_mh hsas_mh (fun t v h => (hnonull_aux t v h).1) hbnd
        (by simpa [muslErrnoAddr, htp_mh] using hal_errno) hphys_mh hgap_mh
        fun s1 altBase e1 hb4k hbAl hbFit hbMap hpc1 hrun1 hsp1 hal1 hcs1 hx0_1 hnv1 hphys1 hbrk1 hbrkS1 hperm1 => ?_
      have htp_s1 : s1.tpidrEl0 = tp := by
        obtain ⟨_, _, htp1, _⟩ := hnv1
        dsimp only [State.setSigAltStack] at htp1
        exact htp1.trans htp_mh
      refine SepWP.weaken_pre_frame
        (P' := (((memRegionProtNone altBase 4096 ∗ memRegion (altBase + 4096#64) (hbExpectedAltRawSz sl.auxvEntries) ∗
          (C.needAltstackAddr ↦₈ 1#8) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
          ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ Pmh_out altBase) ∗ stackAt (s_cm.sp - 0x120#64) 0x220) ∗ G))
        (fun R hm => by
          dsimp only [Pmh_out, muslErrnoAddr] at hm ⊢
          rw [htp_s1] at hm
          rw [← hsp_mh, stackAt_split_bottom s_mh.sp 0xd0 336 (by decide)]
          refine Satisfies.mono ?_ hm
          refine Entails.trans (Q := ((tp - 0xa4#64) ↦₃₂ e1) ∗ ?Rest) (by sep_frame) ?_
          refine Entails.trans (sepConj_mono_left (Entails.sepExists_right e1 (Entails.refl _))) (by sep_entail))
        (hk s1 altBase hb4k hbAl hbFit
          (by rwa [Memory.canMap_congr (funext hvm_mh.perm_eq)] at hbMap)
          hpc1 hrun1 hsp1 hal1 hcs1 hx0_1 hnv1
          (hphys1.trans (by rw [hvm_mh.physMemAvail_eq]))
          (hbrk1.trans hvm_mh.brk_eq) (hbrkS1.trans hvm_mh.brkStart_eq)
          (fun a => by
            dsimp only [sl]
            rw [hperm1 a]
            simp only [Memory.perm_setPermNonFrozen, Memory.perm_mapZero, hvm_mh.perm_eq]))
    · intro s_post s0' G hsp_post hpc0 hrun0 hsp0 hal0 hlr0 hx0_0 hx1_0 hx2_0 _ hk
      refine step_hb_sigaction_wrap (hb_hasInstrs_withSvc hsig_fast)
        (actOpt := some (11#32, hbCustomSigAction C S))
        (Pin := ((s_post.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s_post.sp + 8#64) ↦₆₄ 0#64) ∗ ((s_post.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ Pin11)
        (Pout := fun _ => ((s_post.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s_post.sp + 8#64) ↦₆₄ 0#64) ∗ ((s_post.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ Pcustom11)
        (F := G) (fun _ hm => by rw [hsp0]; rw [sepConj_assoc] at hm; exact hm)
        hpc0 hrun0 hal0 hlr0 hx0_0 hx1_0 hx2_0 (Or.inr (Or.inl rfl))
        (fun si Gi hpci hruni hspi hali hlri hx0i hx1i hx2i _ hki => ?_)
        (fun sf _ hpcf hrunf hspf half hcsf hx0f hnvf => by rw [hsp0]; exact hk sf hpcf hrunf (hspf.trans hsp0) half hcsf hx0f hnvf)
      have hspi_lo : 0x90 ≤ si.sp.toNat := by
        rw [hspi, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hsp0, hsp_post, hsp_sub150_nat]; exact Nat.le_trans (by decide) hsp_sub150_lo)),
            hsp0, hsp_post, hsp_sub150_nat]; exact hsp_sub150_80_lo
      have hact_ne : s_post.sp ≠ 0#64 := fun heq => by
        have h0 := congrArg BitVec.toNat heq; rw [hsp_post, hsp_sub150_nat] at h0
        exact hsp_sub150_ne0 h0
      exact step_hb_libcSigaction_custom (hsLo := 0#32) (unmask0 := 0#32) (eintr0 := 0#32)
        (Or.inr rfl) (hasCode_withSvc hlsa_head)
        (hb_hasInstrs_withSvc hlsa_mid) (hb_hasInstrs_withSvc hlsa_tail)
        (hasCode_withSvc hret) (hb_hasInstrs_withSvc cPre.memOps.memcpy)
        hal_hs hsig_gt1 hpci hruni hali hspi_lo hlri hx0i hx1i hx2i
        (Or.inl rfl) hact_ne (Or.inl rfl)
        fun s1 hpc1 hrun1 hsp1 hal1 hcs1 hx0_1 hnv1 => hki s1 0#64 hpc1 hrun1 hsp1 hal1 hcs1 hx0_1 hnv1
    · intro s_post s0' G hsp_post hsig7_post hpc0 hrun0 hsp0 hal0 hlr0 hx0_0 hx1_0 hx2_0 hnv0 hk
      refine step_hb_sigaction_wrap (hb_hasInstrs_withSvc hsig_fast) (actOpt := none)
        (Pin := (s_post.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s_post.sp + 8#64) ↦₆₄ 0#64) ∗ ((s_post.sp + 0x88#64) ↦₆₄ 0x08000004#64))
        (Pout := fun _ => (s_post.sp ↦₆₄ 0#64) ∗ ((s_post.sp + 8#64) ↦₆₄ 0#64) ∗ ((s_post.sp + 0x88#64) ↦₆₄ 0#64))
        (F := G) (fun _ hm => by rw [hsp0]; rw [sepConj_assoc] at hm; exact hm)
        hpc0 hrun0 hal0 hlr0 hx0_0 hx1_0 hx2_0 (Or.inr (Or.inr rfl))
        (fun si Gi hpci hruni hspi hali hlri hx0i hx1i hx2i hnvi hki => ?_)
        (fun sf _ hpcf hrunf hspf half hcsf hx0f hnvf => by rw [hsp0]; exact hk sf hpcf hrunf (hspf.trans hsp0) half hcsf hx0f hnvf)
      have hspi_lo : 0x90 ≤ si.sp.toNat := by
        rw [hspi, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hsp0, hsp_post, hsp_sub150_nat]; exact Nat.le_trans (by decide) hsp_sub150_lo)),
            hsp0, hsp_post, hsp_sub150_nat]; exact hsp_sub150_80_lo
      have hoact_ne : s_post.sp ≠ 0#64 := fun heq => by
        have h0 := congrArg BitVec.toNat heq; rw [hsp_post, hsp_sub150_nat] at h0
        exact hsp_sub150_ne0 h0
      have hsig7 : si.getSigAction 7#32 = {} := by
        rw [State.getSigAction, hnvi.2.2.2.1, hnv0.2.2.2.1]
        simpa [State.setSigAction, State.getSigAction, htls.2.2.1, hinfo.s0_sigActions] using hsig7_post
      exact step_hb_libcSigaction_probe_zero (Or.inr rfl) (hasCode_withSvc hlsa_head) (hb_hasInstrs_withSvc hlsa_tail)
        (hasCode_withSvc hret) (hb_hasInstrs_withSvc cPre.memOps.memcpy) hpci hruni hali hspi_lo hlri hx0i hx1i hx2i
        (Or.inr rfl) hoact_ne hsig7 rfl fun s1 hpc1 hrun1 hsp1 hal1 hcs1 hx0_1 hnv1 => hki s1 0#64 hpc1 hrun1 hsp1 hal1 hcs1 hx0_1 hnv1
    · intro s_post s1 s0' G hsp_post hs1_sp _ hpc0 hrun0 hsp0 hal0 hlr0 hx0_0 hx1_0 hx2_0 _ hk
      refine step_hb_sigaction_wrap (hb_hasInstrs_withSvc hsig_fast)
        (actOpt := some (7#32, hbCustomSigAction C S))
        (Pin := ((s1.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s1.sp + 8#64) ↦₆₄ 0#64) ∗ ((s1.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ Pcustom11)
        (Pout := fun _ => ((s1.sp ↦₆₄ S.signalHandlerAddr) ∗ ((s1.sp + 8#64) ↦₆₄ 0#64) ∗ ((s1.sp + 0x88#64) ↦₆₄ 0x08000004#64)) ∗ Pcustom7)
        (F := G) (fun _ hm => by rw [hsp0]; rw [sepConj_assoc] at hm; exact hm)
        hpc0 hrun0 hal0 hlr0 hx0_0 hx1_0 hx2_0 (Or.inr (Or.inr rfl))
        (fun si Gi hpci hruni hspi hali hlri hx0i hx1i hx2i _ hki => ?_)
        (fun sf _ hpcf hrunf hspf half hcsf hx0f hnvf => by rw [hsp0]; exact hk sf hpcf hrunf (hspf.trans hsp0) half hcsf hx0f hnvf)
      have hspi_lo : 0x90 ≤ si.sp.toNat := by
        rw [hspi, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hsp0, hs1_sp, hsp_post, hsp_sub150_nat]; exact Nat.le_trans (by decide) hsp_sub150_lo)),
            hsp0, hs1_sp, hsp_post, hsp_sub150_nat]; exact hsp_sub150_80_lo
      have hact_ne : s1.sp ≠ 0#64 := fun heq => by
        have h0 := congrArg BitVec.toNat heq; rw [hs1_sp, hsp_post, hsp_sub150_nat] at h0
        exact hsp_sub150_ne0 h0
      exact step_hb_libcSigaction_custom (hsLo := 0x400#32) (unmask0 := 1#32) (eintr0 := 1#32)
        (Or.inr rfl) (hasCode_withSvc hlsa_head)
        (hb_hasInstrs_withSvc hlsa_mid) (hb_hasInstrs_withSvc hlsa_tail)
        (hasCode_withSvc hret) (hb_hasInstrs_withSvc cPre.memOps.memcpy)
        hal_hs hsig_gt1 hpci hruni hali hspi_lo hlri hx0i hx1i hx2i
        (Or.inr rfl) hact_ne (Or.inr rfl)
        fun s2 hpc2 hrun2 hsp2 hal2 hcs2 hx0_2 hnv2 => hki s2 0#64 hpc2 hrun2 hsp2 hal2 hcs2 hx0_2 hnv2
    · intro sf altBase hb4k hbAl hbFit hbMap hpc_f hrun_f hsp_f hal_f _ hlr_f hfs_f htr_f htp_f hphys_f hbrk_f hbrkS_f hperm_f
      dsimp only [Pmh_out, HbAltstackMappedPre]
      wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro e0
      apply SepWP.done hpc_f hrun_f
      refine ⟨altBase, e0, hb4k, hbAl, hbFit, hbMap, hsp_f, hal_f, hlr_f, htp_f,
        hfs_f.trans (htls.1.trans hinfo.s0_fs), htr_f.trans (htls.2.1.trans hinfo.s0_trace),
        hphys_f.trans (by rw [htls.2.2.2.2.2.1, hinfo.s0_physMemAvail]),
        hbrk_f.trans (htls.2.2.2.1.trans (hinfo.s0_brk.trans (hbrk_eq.trans hv.brkBase_eq.symm))),
        hbrkS_f.trans (htls.2.2.2.2.1.trans (hinfo.s0_brkStart.trans (hbrk_eq.trans hv.brkBase_eq.symm))),
        hperm_f, ?_⟩
      refine Entails.trans (Q := ((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ HbThreadIdInv C tp ∗
        ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
        ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
        (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        ((tp - 0xa4#64) ↦₃₂ e0) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
        HbAltstackInv4k C S (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
        memMapped altBase (4096 + hbExpectedAltRawSz sl.auxvEntries) ∗
        HbCallerFrames C sl.sp0 ∗ stackAt (sl.sp0 - 0x170#64) 0x200) ∗ ?R_dead)
        (by sep_frame) ?_
      refine Entails.trans (Q := (C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ HbThreadIdInv C tp ∗
        ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
        ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
        (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        ((tp - 0xa4#64) ↦₃₂ e0) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
        HbAltstackInv4k C S (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
        memMapped altBase (4096 + hbExpectedAltRawSz sl.auxvEntries) ∗
        HbCallerFrames C sl.sp0 ∗ stackAt (sl.sp0 - 0x170#64) 0x200 ∗ ?R_dead)
        (by sep_entail)
        (by iterate 11 apply sepConj_mono_right
            exact Entails.sepExists_right _ (Entails.refl _))
  obtain ⟨s_main, hsteps, ⟨hpc_m, hrun_m, Pf, hm_m, altBase, e0, hb4k, hbAl, hbFit, hbMap,
    hsp_m, hal_m, hlr_m, htp_m, hfs_m, htr_m, hphys_m, hbrk_m, hbrkS_m, hperm_m, hent_m⟩ | ⟨_, hfalse⟩⟩ :=
    SepWP.to_reaches_pc hwp hsat_cm hcode_cm
  · exact ⟨s_main, altBase, e0, hsteps, hb4k, hbAl, hbFit, hbMap, hpc_m, hrun_m, hsp_m, hal_m, hlr_m,
      htp_m, hfs_m, htr_m, hphys_m, hbrk_m, hbrkS_m, hperm_m,
      Satisfies.mono (sepConj_mono_left hent_m) hm_m⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

private theorem hb_countPerm_add (m : Memory) (p : Option Perm → Bool) :
    ∀ (addr : BitVec 64) (n1 n2 : Nat),
      m.countPerm p addr (n1 + n2) =
        m.countPerm p addr n1 + m.countPerm p (addr + BitVec.ofNat 64 n1) n2
  | addr, 0, n2 => by simp [Memory.countPerm]
  | addr, n1 + 1, n2 => by
    rw [Nat.succ_add, Memory.countPerm, Memory.countPerm,
        hb_countPerm_add m p (addr + 1#64) n1 n2,
        show addr + 1#64 + BitVec.ofNat 64 n1 = addr + BitVec.ofNat 64 (n1 + 1) by bv_omega]
    omega

private theorem hb_countPerm_eq_len (m : Memory) (p : Option Perm → Bool) :
    ∀ (addr : BitVec 64) {n : Nat},
      (∀ i < n, p (m.perm (addr + BitVec.ofNat 64 i)) = true) →
      m.countPerm p addr n = n
  | addr, 0, _ => rfl
  | addr, n + 1, h => by
    have h0 : p (m.perm addr) = true := by simpa using h 0 (Nat.zero_lt_succ n)
    have hrest : m.countPerm p (addr + 1#64) n = n :=
      hb_countPerm_eq_len m p (addr + 1#64) fun i hi => by
        simpa [show addr + 1#64 + BitVec.ofNat 64 i = addr + BitVec.ofNat 64 (i + 1) by bv_omega]
          using h (i + 1) (Nat.succ_lt_succ hi)
    simp only [Memory.countPerm, h0, ↓reduceIte, hrest]; omega

private theorem hb_s_main_perm_rw_of_s0 {s0 s_cm s_main : State}
    {altBase : BitVec 64} {altRawSz : Nat} {a : BitVec 64}
    (hbMap : s_cm.mem.canMap altBase (altRawSz + 4096) = true)
    (hperm_cm : ∀ x, s_cm.mem.perm x = s0.mem.perm x)
    (hperm_m : ∀ x, s_main.mem.perm x =
      ((s_cm.mem.mapZero altBase (altRawSz + 4096)).setPermNonFrozen altBase 4096 Perm.protNone).perm x)
    (ha : s0.mem.perm a = some Perm.rw) :
    s_main.mem.perm a = some Perm.rw := by
  have hcm : s_cm.mem.perm a = some Perm.rw := (hperm_cm a).trans ha
  have hnot4k : ¬ (a - altBase).toNat < 4096 := fun hlt => by
    have hunmap := (Memory.allPerm_iff s_cm.mem (fun p => !p.mapped) altBase (altRawSz + 4096)).mp
      hbMap (a - altBase).toNat (by omega)
    rw [show altBase + BitVec.ofNat 64 (a - altBase).toNat = a by bv_omega, hcm] at hunmap
    cases hunmap
  rw [hperm_m a, Memory.perm_setPermNonFrozen]
  simp only [hnot4k, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [Memory.perm_mapZero, hcm, ite_self]

private theorem hb_stack_mid_le (img : ElfImage) {inputs : ProcessInputs} {s0 : State}
    (hvalid : inputs.Valid) (hinfo : InitialStackInfo img inputs s0) :
    (StackLayout.of img inputs).argvBase.toNat -
      (StackLayout.of img inputs).auxvTableAddr.toNat ≤ 447 := by
  have htop48 : inputs.init.stackTop.toNat ≤ 2 ^ 48 := hinfo.stackTop_align.2.2
  have h48_lt : (2 ^ 48 : Nat) < 2 ^ 64 := by decide
  have han := hinfo.addrs_nat; dsimp only at han
  obtain ⟨_, _, haux_nat, _, hplat_nat, hargvB_nat, _, _, _⟩ := han
  have hwf_aux := mkAuxvEntries_wf img hvalid.auxv
    (StackLayout.of img inputs).platformAddr
    (StackLayout.of img inputs).randomAddr
    (StackLayout.of img inputs).execfnAddr
  have haux_len_le : (StackLayout.of img inputs).auxvEntries.length ≤ 24 := by
    rw [hinfo.auxvEntries_eq]; exact hwf_aux.2.1
  have hav_len := hinfo.argvAddrs_length
  have hev_len := hinfo.envpAddrs_length
  have hpad_le : (StackLayout.of img inputs).infoPadLen ≤ 15 :=
    (fun n => (by unfold alignUp16; omega : alignUp16 n - n ≤ 15)) _
  let unpad : List (BitVec 64) :=
    ([BitVec.ofNat 64 inputs.argv.length] ++ (StackLayout.of img inputs).argvAddrs ++ [0#64] ++
      (StackLayout.of img inputs).envpAddrs ++ [0#64]) ++
      (((StackLayout.of img inputs).auxvEntries ++ [(AuxvTag.null, 0#64)]).flatMap fun (t, v) => [t, v])
  let tw : List (BitVec 64) :=
    if unpad.length % 2 == 0 then unpad else unpad ++ [0#64]
  have hrand_sp0 : ∃ ib ≤ inputs.init.stackTop.toNat,
      (StackLayout.of img inputs).randomAddr = BitVec.ofNat 64 ib ∧
      (StackLayout.of img inputs).sp0 = BitVec.ofNat 64 (ib - (tw.flatMap (Obj.bytesLE 8)).length) :=
    ⟨_, Nat.sub_le _ _, rfl, rfl⟩
  obtain ⟨ib, hib_le, hrand_eq, hsp0_eq⟩ := hrand_sp0
  have hrand_nat : (StackLayout.of img inputs).randomAddr.toNat = ib := by
    rw [hrand_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsp0_nat : (StackLayout.of img inputs).sp0.toNat = ib - (tw.flatMap (Obj.bytesLE 8)).length := by
    rw [hsp0_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have htw_bytes : (tw.flatMap (Obj.bytesLE 8)).length = 8 * tw.length :=
    flatMap_bytesLE8_length tw
  have htw_len : tw.length ≤ unpad.length + 1 := by dsimp only [tw]; split <;> simp
  have hpairs : ∀ ps : List (BitVec 64 × BitVec 64),
      (ps.flatMap fun (t, v) => [t, v]).length = 2 * ps.length := fun ps => by
    induction ps with
    | nil => rfl
    | cons p rs ih => rcases p with ⟨t, v⟩; simp [ih]; omega
  have hunpad_len : unpad.length =
      inputs.argv.length + inputs.envp.length + 3 + 2 * ((StackLayout.of img inputs).auxvEntries.length + 1) := by
    dsimp only [unpad]
    simp only [List.length_append, List.length_cons, List.length_nil, hav_len, hev_len, hpairs]
    omega
  clear hvalid hinfo hwf_aux
  omega

private theorem hb_stack_rwBytes_bound {img : ElfImage} {inputs : ProcessInputs}
    {s0 s_cm s_main : State} {altBase : BitVec 64}
    (hvalid : inputs.Valid) (hinfo : InitialStackInfo img inputs s0)
    (hbMap : s_cm.mem.canMap altBase
      (hbExpectedAltRawSz (StackLayout.of img inputs).auxvEntries + 4096) = true)
    (hperm_cm : ∀ a, s_cm.mem.perm a = s0.mem.perm a)
    (hperm_m : ∀ a, s_main.mem.perm a =
      ((s_cm.mem.mapZero altBase
        (hbExpectedAltRawSz (StackLayout.of img inputs).auxvEntries + 4096)).setPermNonFrozen
        altBase 4096 Perm.protNone).perm a) :
    inputs.init.stackSize ≤ rwBytes s_main.mem + 447 := by
  have hmid := hb_stack_mid_le img hvalid hinfo
  have htop48 : inputs.init.stackTop.toNat ≤ 2 ^ 48 := hinfo.stackTop_align.2.2
  have h48_lt : (2 ^ 48 : Nat) < 2 ^ 64 := by decide
  have hsize_le : inputs.init.stackSize ≤ inputs.init.stackTop.toNat := by
    have hfl := hinfo.stackBase_floor; unfold STACK_BASE_MIN at hfl; omega
  have hhr := hinfo.sp0_headroom.2
  have han := hinfo.addrs_nat; dsimp only at han
  obtain ⟨hargvT_nat, henvpT_nat, haux_nat, haux_le, hplat_nat, hargvB_nat, _, _, hupper_top⟩ := han
  have hav_len := hinfo.argvAddrs_length
  have hev_len := hinfo.envpAddrs_length
  have hperm_low := hinfo.s0_perm_rw_below_sp0
  have hc_argc := hinfo.holds_argc
  have hc_argv := hinfo.holds_argv
  have hc_envp := hinfo.holds_envp
  have hc_upper := hinfo.holds_upperStr
  clear hinfo hvalid
  generalize hL : StackLayout.of img inputs = sl at *
  clear hL
  let sb := inputs.init.stackTop.toNat - inputs.init.stackSize
  let len1 := sl.auxvTableAddr.toNat - sb
  let mid := sl.argvBase.toNat - sl.auxvTableAddr.toNat
  let len2 := inputs.init.stackTop.toNat - sl.argvBase.toNat
  let rem := 2 ^ 64 - inputs.init.stackTop.toNat
  have hb1_eq : 0#64 + BitVec.ofNat 64 sb = BitVec.ofNat 64 sb := BitVec.zero_add _
  have hb2_eq : 0#64 + BitVec.ofNat 64 sb + BitVec.ofNat 64 len1 + BitVec.ofNat 64 mid = sl.argvBase := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    dsimp only [sb, len1, mid]
    omega
  have hb_add_sub : ∀ (x y : BitVec 64), x.toNat ≤ y.toNat → x + BitVec.ofNat 64 (y.toNat - x.toNat) = y := by
    intro x y hxy; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := y.isLt; omega
  have hs0_seg1 : ∀ i < len1, s0.mem.perm (BitVec.ofNat 64 sb + BitVec.ofNat 64 i) = some Perm.rw := by
    intro i hi
    dsimp only [len1] at hi
    let a := BitVec.ofNat 64 sb + BitVec.ofNat 64 i
    have ha_nat : a.toNat = sb + i := by
      simp only [a, BitVec.toNat_add, BitVec.toNat_ofNat]
      dsimp only [sb] at hi ⊢; omega
    by_cases h1 : a.toNat < sl.sp0.toNat
    · exact hperm_low a (by dsimp only [sb] at ha_nat; omega) h1
    · by_cases h2 : a.toNat < sl.argvTableAddr.toNat
      · have hj : a.toNat - sl.sp0.toNat < (Obj.bytesLE 8 (BitVec.ofNat 64 inputs.argv.length)).length := by
          simp only [Obj.bytesLE, List.length_map, List.length_range]; omega
        have hcell := (hc_argc (a.toNat - sl.sp0.toNat) hj).2.1
        rwa [hb_add_sub sl.sp0 a (by omega)] at hcell
      · by_cases h3 : a.toNat < sl.envpTableAddr.toNat
        · have hj : a.toNat - sl.argvTableAddr.toNat <
              (((sl.argvAddrs ++ [0#64]).flatMap (Obj.bytesLE 8))).length := by
            rw [flatMap_bytesLE8_length, List.length_append, List.length_singleton, hav_len]; omega
          have hcell := (hc_argv (a.toNat - sl.argvTableAddr.toNat) hj).2.1
          rwa [hb_add_sub sl.argvTableAddr a (by omega)] at hcell
        · have hj : a.toNat - sl.envpTableAddr.toNat <
              (((sl.envpAddrs ++ [0#64]).flatMap (Obj.bytesLE 8))).length := by
            rw [flatMap_bytesLE8_length, List.length_append, List.length_singleton, hev_len]; omega
          have hcell := (hc_envp (a.toNat - sl.envpTableAddr.toNat) hj).2.1
          rwa [hb_add_sub sl.envpTableAddr a (by omega)] at hcell
  have hc1 : s_main.mem.countPerm (· == some Perm.rw) (BitVec.ofNat 64 sb) len1 = len1 :=
    hb_countPerm_eq_len s_main.mem _ _ fun i hi =>
      beq_iff_eq.mpr (hb_s_main_perm_rw_of_s0 hbMap hperm_cm hperm_m (hs0_seg1 i hi))
  have hc2 : s_main.mem.countPerm (· == some Perm.rw) sl.argvBase len2 = len2 :=
    hb_countPerm_eq_len s_main.mem _ _ fun i hi =>
      beq_iff_eq.mpr (hb_s_main_perm_rw_of_s0 hbMap hperm_cm hperm_m
        ((hc_upper i (by dsimp only [len2] at hi; omega)).2.1))
  have hrw_ge : len1 + len2 ≤ rwBytes s_main.mem := by
    unfold rwBytes Memory.countRw
    rw [show (2 ^ 64 : Nat) = sb + (len1 + (mid + (len2 + rem))) by dsimp only [sb, len1, mid, len2, rem]; omega,
        hb_countPerm_add, hb_countPerm_add, hb_countPerm_add, hb_countPerm_add,
        hb2_eq, hb1_eq, hc1, hc2]
    omega
  dsimp only [sb, len1, mid, len2] at hmid hrw_ge
  omega

set_option maxHeartbeats 400000 in
private theorem hbStartup_initHeap_at_main {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {mpl : Obj.MultiPlacement} {img : ElfImage} {inputs : ProcessInputs}
    {s0 s_cm s_main : State} {altBase : BitVec 64} {e0 : BitVec 32} {R : SepProp}
    (hv : C.Valid) (hS : S.Valid C) (hm : HbMatchesImage C S img = true)
    (hpl : HbMallocngPlaced P C mpl) (hvalid : inputs.Valid) (hbudget : HashbrownStdinBudget inputs)
    (hinfo : InitialStackInfo img inputs s0)
    (hbMap : s_cm.mem.canMap altBase
      (hbExpectedAltRawSz (StackLayout.of img inputs).auxvEntries + 4096) = true)
    (hperm_cm : ∀ a, s_cm.mem.perm a = s0.mem.perm a)
    (htp_m : s_main.tpidrEl0 = C.std.builtinTlsAddr + 0xc8#64)
    (hphys_m : s_main.physMemAvail =
      inputs.init.physMemAvail - (hbExpectedAltRawSz (StackLayout.of img inputs).auxvEntries + 4096))
    (hbrk_m : s_main.brk = C.mallocng.brkBase) (hbrkS_m : s_main.brkStart = C.mallocng.brkBase)
    (hperm_m : ∀ a, s_main.mem.perm a =
      ((s_cm.mem.mapZero altBase
        (hbExpectedAltRawSz (StackLayout.of img inputs).auxvEntries + 4096)).setPermNonFrozen
        altBase 4096 Perm.protNone).perm a)
    (hSat : s_main.mem ⊨ MallocngInitialBss C.mallocng ∗
      (C.mallocng.roTablesAddr ↦ᵣ ProofLib.mallocngRoTablesBytes) ∗
      ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗
      ((C.std.libcAddr + 0x08#64) ↦₆₄ (StackLayout.of img inputs).auxvTableAddr) ∗
      ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
      ((StackLayout.of img inputs).auxvTableAddr ↦ₛ
        encodeAuxvBytes (StackLayout.of img inputs).auxvEntries) ∗
      ((StackLayout.of img inputs).randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗
      (((C.std.builtinTlsAddr + 0xc8#64) - 0xa4#64) ↦₃₂ e0) ∗ R) :
    let sl := StackLayout.of img inputs
    ∃ (γ : GhostName) (e1 : BitVec 32),
      s_main.mem ⊨ (hbMallocngIface hpl hbudget.1).Heap γ 0 0 s_main ∗
        HbAuxvTicket γ sl.auxvTableAddr sl.auxvEntries ∗
        (muslErrnoAddr s_main ↦₃₂ e1) ∗
        (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes.take 8) ∗ R := by
  dsimp only
  let sl := StackLayout.of img inputs
  obtain ⟨hwf, _, _, _, hbrk_eq, ⟨hbrk_lo, hbrk_hi⟩, _, _⟩ := HbMatchesImage.unpack hm
  have hbrk_img_nat : img.brkStart.toNat = C.std.brkStart.toNat := congrArg BitVec.toNat hbrk_eq
  have hbrk_base_nat : C.mallocng.brkBase.toNat = img.brkStart.toNat :=
    congrArg BitVec.toNat (hv.brkBase_eq.trans hbrk_eq.symm)
  have hsize_le : inputs.init.stackSize ≤ inputs.init.stackTop.toNat := by
    have hfl := hinfo.stackBase_floor; unfold STACK_BASE_MIN at hfl; omega
  have hstackCeil : inputs.init.stackSize ≤ 128 * 2 ^ 20 := by
    have hle := hvalid.stackSize_le; unfold STACK_SIZE_MAX at hle; omega
  have hmwf0 := hinfo.mallocngInitialMemWf (hv.brkBase_eq.trans hbrk_eq.symm)
    (by omega) (by omega) hsize_le hstackCeil hwf
  have hBrkWf : MallocngBrkStartWf C.mallocng.brkBase :=
    ⟨by unfold MMAP_MIN_ADDR; omega, hmwf0.2.2.1, by omega⟩
  have hbnd : ∀ e ∈ sl.auxvEntries, e.1 = 51#64 → e.2.toNat ≤ 524288 := by
    dsimp only [sl]; rw [hinfo.auxvEntries_eq]
    exact hbAuxv_minsigstksz_le hvalid sl.platformAddr sl.randomAddr sl.execfnAddr
  have ⟨_, _, hrawHi⟩ := hbExpectedAltRawSz_spec hbnd
  have halt_sz_le : hbExpectedAltRawSz sl.auxvEntries + 4096 ≤ 528384 :=
    Nat.add_le_add_right hrawHi 4096
  let staticIvs : List (BitVec 64 × Nat) :=
    [(0#64, C.mallocng.brkBase.toNat),
     (BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize), inputs.init.stackSize),
     (altBase, hbExpectedAltRawSz sl.auxvEntries + 4096)]
  have hMapped : ∀ a : BitVec 64, (s_main.mem.perm a).mapped = true → MallocngInIntervals staticIvs a := by
    intro a ha
    have h := hbMapped_inIntervals hmwf0 (by omega) hperm_cm hperm_m a ha
    rwa [show inputs.init.stackTop.toNat - (inputs.init.stackTop.toNat - inputs.init.stackSize) =
      inputs.init.stackSize by omega] at h
  have hStPhys : (staticIvs.map Prod.snd).sum ≤ 133 * 2 ^ 20 ∧
      (staticIvs.map Prod.snd).sum + hbDynPhysBudget inputs.stdin.length ≤ physPlusRw s_main := by
    have hbrk3m : C.mallocng.brkBase.toNat ≤ 3 * 2 ^ 20 := hpl.brkBase_le
    have hstkRw : inputs.init.stackSize ≤ rwBytes s_main.mem + 447 :=
      hb_stack_rwBytes_bound hvalid hinfo hbMap hperm_cm hperm_m
    simp only [staticIvs, List.map, List.sum_cons, List.sum_nil]
    refine ⟨(fun (a b c : Nat) (ha : a ≤ 3 * 2 ^ 20) (hb : b ≤ 128 * 2 ^ 20) (hc : c ≤ 528384) =>
      (by omega : a + (b + (c + 0)) ≤ 133 * 2 ^ 20)) _ _ _ hbrk3m hstackCeil halt_sz_le, ?_⟩
    rw [physPlusRw, hbDynPhysBudget, hphys_m]
    exact (fun (a b c L p r : Nat) (ha : a ≤ 3 * 2 ^ 20) (hb : b ≤ r + 447) (hc : c ≤ 528384)
        (hp : 8 * 2 ^ 20 + 8 * L ≤ p) =>
      (by omega : a + (b + (c + 0)) + (4185665 + 8 * L) ≤ p - c + r))
      _ _ _ _ _ _ hbrk3m hstkRw halt_sz_le hbudget.2
  have hrand16 := hvalid.auxv.random16; have hsp16 := hinfo.sp0_align16
  have htop48 : inputs.init.stackTop.toNat ≤ 2 ^ 48 := hinfo.stackTop_align.2.2
  have han := hinfo.addrs_nat; dsimp only at han
  obtain ⟨_, _, haux_nat, haux_le, hplat_nat, hargvB_nat, _, _, hupper_top⟩ := han
  obtain ⟨prePairs, sufPairs, hsplit_eq, _, hps_le, hpre_no, hsuf_no⟩ :=
    mkAuxvEntries_split_random img hvalid.auxv sl.platformAddr sl.randomAddr sl.execfnAddr
  have hauxE_split : sl.auxvEntries = prePairs ++ [(AuxvTag.random, sl.randomAddr)] ++ sufPairs :=
    hinfo.auxvEntries_eq.trans hsplit_eq
  have hauxE_len : sl.auxvEntries.length = prePairs.length + sufPairs.length + 1 := by
    rw [hauxE_split]; simp; omega
  rw [hauxE_len] at haux_le
  have htp_nat : s_main.tpidrEl0.toNat = C.std.builtinTlsAddr.toNat + 0xc8 := by
    rw [htp_m, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := hS.builtinTls_noWrap; omega),
        Nat.mod_eq_of_lt (by have := hS.builtinTls_noWrap; omega)]
  have hsh_pure : (inputs.init.auxv.randomBytes.drop 8).length = 8 ∧
      0xa4 ≤ s_main.tpidrEl0.toNat ∧ s_main.tpidrEl0.toNat ≤ 2 ^ 48 ∧
      prePairs.length + sufPairs.length ≤ 64 ∧ sl.auxvTableAddr.toNat % 8 = 0 ∧
      sl.auxvTableAddr.toNat + 16 * (prePairs.length + sufPairs.length + 2) ≤ 2 ^ 48 ∧
      sl.randomAddr.toNat + 16 ≤ 2 ^ 48 ∧
      (∀ e ∈ prePairs, e.1 ≠ AuxvTag.null ∧ e.1 ≠ AuxvTag.random) ∧
      (∀ e ∈ sufPairs, e.1 ≠ AuxvTag.null ∧ e.1 ≠ AuxvTag.random) :=
    ⟨by simp [hrand16], by have := hS.builtinTls_lo; omega, by have := hS.builtinTls_noWrap; omega,
     hps_le, by dsimp only [sl] at *; omega, by dsimp only [sl] at *; omega,
     by dsimp only [sl] at *; omega, hpre_no, hsuf_no⟩
  have hSat_split := hSat
  rw [split_random_hi8 sl.randomAddr hrand16, hauxE_split] at hSat_split
  have hSat_init : s_main.mem ⊨ MallocngInitialBss C.mallocng ∗
      MallocngStartupInputs C.mallocng sl.auxvTableAddr sl.randomAddr prePairs sufPairs
        (inputs.init.auxv.randomBytes.drop 8) e0 s_main ∗
      ((sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes.take 8) ∗ R) := by
    refine Satisfies.mono ?_ hSat_split
    unfold MallocngStartupInputs muslErrnoAddr
    rw [pure_sepConj_of_true hsh_pure, hv.needLocks_eq, hv.auxv_eq, hv.pageSize_eq, htp_m]; sep_entail
  obtain ⟨γ, e1, hγ⟩ := hbInitHeapTracked (staticIvs := staticIvs) hpl hbudget.1 hbrk_m hbrkS_m
    hBrkWf (Nat.le_refl 3) hStPhys hMapped hSat_init
  rw [← hauxE_split] at hγ
  exact ⟨γ, e1, by simpa only [sepConj_assoc] using hγ⟩

set_option maxHeartbeats 400000 in
theorem hbStartup_to_userMain {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {mpl : Obj.MultiPlacement} {img : ElfImage} {inputs : ProcessInputs}
    (cPre : HbPreMainCode P C S) (hv : C.Valid) (hS : S.Valid C)
    (hm : HbMatchesImage C S img = true) (hpl : HbMallocngPlaced P C mpl)
    (hvalid : inputs.Valid) (hbudget : HashbrownStdinBudget inputs)
    (hrx : C.std.rxProgram img = P := by rfl) :
    let sl := StackLayout.of img inputs
    let M := hbMallocngIface hpl hbudget.1
    let haveLse : BitVec 8 := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8
    ∃ (s0 s_main : State) (altBase : BitVec 64) (γ : GhostName) (e_init : BitVec 32),
      img.loadState inputs = .ok s0 ∧ P.CodeLoaded s0.mem ∧ Steps P s0 s_main ∧
      HbUserMainState P C.std img inputs s0 s_main ∧
      4096 ≤ altBase.toNat ∧ altBase.toNat % 4096 = 0 ∧
      altBase.toNat + (hbExpectedAltRawSz sl.auxvEntries + 4096) ≤ 2 ^ 48 ∧
      (∀ t v, (t, v) ∈ sl.auxvEntries → t ≠ 0#64) ∧ hbAltstackReqSz sl.auxvEntries ≤ 524288 ∧
      (s_main.mem ⊨
        (hbRodata C.hbPl ∗ M.Heap γ 0 0 s_main ∗ HbStdoutInv C M.toMallocngCoreIface γ false ∗
          HbStdinUninit C ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbCliRoData C ∗
          (muslErrnoAddr s_main ↦₃₂ e_init) ∗ HbThreadIdInv C s_main.tpidrEl0 ∗
          (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ stackAt s_main.sp 261984) ∗
        ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
          HbCallerFrames C sl.sp0 ∗ HbPostMainGlobals C S ∗
          HbAltstackInv4k C S (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
          HbAltstackMappedPre (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
          HbAuxvTicket γ sl.auxvTableAddr sl.auxvEntries ∗
          stackAt (s_main.sp - 261984#64) 261936 ∗ ∃∗ R_unused : SepProp, R_unused)) := by
  dsimp only
  let sl := StackLayout.of img inputs
  let M := hbMallocngIface hpl hbudget.1
  let haveLse : BitVec 8 := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8
  let tp := C.std.builtinTlsAddr + 0xc8#64
  obtain ⟨hwf, _, _, _, hbrk_eq, ⟨_, hbrk_hi⟩, _, _⟩ := HbMatchesImage.unpack hm
  have hbrk_img_nat : img.brkStart.toNat = C.std.brkStart.toNat := congrArg BitVec.toNat hbrk_eq
  obtain ⟨s0, hload⟩ := loadState_ok_of_valid_low_brk img hvalid hwf
    (Nat.le_trans (by omega : img.brkStart.toNat ≤ 5 * 2 ^ 20) (by decide : 5 * 2 ^ 20 ≤ STACK_BASE_MIN))
  obtain ⟨s_cm, hinfo, hcode0, hsteps_cm, hpc_cm, hrun_cm, hsp_cm, hal_cm, hlr_cm,
    hx0_cm, hx1_cm, htp_cm, hsas_cm, htls_cm, hm_cm0⟩ :=
    hbLoad_to_cMain cPre hS hm hvalid hload hrx
  have hm_cm1 : s_cm.mem ⊨ (∃∗ R_st12 : SepProp, R_st12) ∗
      (stackAt sl.sp0 48 ∗ memRegion (sl.sp0 - 524288#64) 523408 ∗ stackAt (sl.sp0 - 0x30#64) 0x340 ∗
        (C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
        ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗
        (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗ ((tp - 0xa4#64) ↦₃₂ 0#32) ∗
        ((tp + 0x58#64) ↦₆₄ 0#64) ∗ HbLangStartGlobalsPre C S ∗ HbUserMainGlobalsPre C ∗
        HbPostMainGlobalsNoPs C S) :=
    Satisfies.mono (by dsimp only [tp]; sep_entail) hm_cm0
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_cm1; obtain ⟨R_st12, hm_cm⟩ := hm_cm1
  let R_cm : SepProp :=
    memRegion (sl.sp0 - 524288#64) 523408 ∗ ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗
    (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗ HbUserMainGlobalsPre C ∗
    HbPostMainGlobalsNoPs C S ∗ R_st12
  have hsat_cm : s_cm.mem ⊨
      (stackAt sl.sp0 48 ∗ stackAt (sl.sp0 - 0x30#64) 0x340 ∗
        (C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
        ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
        (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗ ((tp - 0xa4#64) ↦₃₂ 0#32) ∗
        ((tp + 0x58#64) ↦₆₄ 0#64) ∗ HbLangStartGlobalsPre C S) ∗ R_cm :=
    Satisfies.mono (by dsimp only [R_cm]; sep_entail) hm_cm
  obtain ⟨s_main, altBase, e0, hsteps_m, hb4k, hbAl, hbFit, hbMap, hpc_m, hrun_m,
    hsp_m, hal_m, hlr_m, htp_m, hfs_m, htr_m, hphys_m, hbrk_m, hbrkS_m, hperm_m, hm_m0⟩ :=
    hbStep_cMain_to_userMain cPre hv hS hm hvalid hbudget hinfo (hsteps_cm.codeLoaded hcode0)
      hpc_cm hrun_cm hsp_cm hal_cm hlr_cm hx0_cm hx1_cm htp_cm htls_cm hsas_cm hsat_cm
  have hsteps_all : Steps P s0 s_main := hsteps_cm.trans hsteps_m
  have hsp0_lo : 262352 ≤ sl.sp0.toNat :=
    Nat.le_trans (by decide : 262352 ≤ STACK_BASE_MIN + 262144)
      (Nat.le_trans (Nat.add_le_add_right hinfo.stackBase_floor 262144) hinfo.sp0_headroom.2)
  have hsp_hr : 261984 ≤ s_main.sp.toNat := by
    rw [hsp_m, BitVec.toNat_sub_of_le (BitVec.le_def.mpr
      (Nat.le_trans (by decide : (0x170#64 : BitVec 64).toNat ≤ 262352) hsp0_lo))]
    exact Nat.sub_le_sub_right hsp0_lo 0x170
  have hsp_va : s_main.sp.toNat ≤ Arm64.USER_VA_LIMIT := by
    have htop48 : inputs.init.stackTop.toNat ≤ 2 ^ 48 := hinfo.stackTop_align.2.2
    have han := hinfo.addrs_nat; dsimp only at han
    obtain ⟨_, _, _, _, _, _, _, _, _⟩ := han
    rw [hsp_m, BitVec.toNat_sub_of_le (BitVec.le_def.mpr
      (Nat.le_trans (by decide : (0x170#64 : BitVec 64).toNat ≤ 262352) hsp0_lo))]
    unfold Arm64.USER_VA_LIMIT; dsimp only [sl]; omega
  have hmainState : HbUserMainState P C.std img inputs s0 s_main :=
    ⟨hsteps_all.codeLoaded hcode0, hsteps_all.keepsFrozen, hpc_m, hrun_m, hsp_m, hal_m,
     hsp_hr, hsp_va, hlr_m, htp_m, hfs_m, htr_m⟩
  have hwf_aux := mkAuxvEntries_wf img hvalid.auxv sl.platformAddr sl.randomAddr sl.execfnAddr
  rw [← hinfo.auxvEntries_eq] at hwf_aux
  have hnonull : ∀ t v, (t, v) ∈ sl.auxvEntries → t ≠ 0#64 := fun t v h => (hwf_aux.2.2 t v h).1
  have hbnd : ∀ e ∈ sl.auxvEntries, e.1 = 51#64 → e.2.toNat ≤ 524288 := by
    dsimp only [sl]; rw [hinfo.auxvEntries_eq]
    exact hbAuxv_minsigstksz_le hvalid sl.platformAddr sl.randomAddr sl.execfnAddr
  have hbnd_req : hbAltstackReqSz sl.auxvEntries ≤ 524288 := by
    unfold hbAltstackReqSz
    let pred : BitVec 64 × BitVec 64 → Bool := fun e => e.1 == 51#64
    change max (((sl.auxvEntries.find? pred).map Prod.snd).getD 0#64).toNat 12288 ≤ 524288
    cases hfind : sl.auxvEntries.find? pred with
    | none => exact Nat.max_le.mpr ⟨Nat.zero_le _, by decide⟩
    | some p =>
      have h51 : pred p = true := List.find?_some hfind
      exact Nat.max_le.mpr ⟨hbnd p (List.mem_of_find?_eq_some hfind) (beq_iff_eq.mp h51), by decide⟩
  have hm_m1 : s_main.mem ⊨ (∃∗ R_ls : SepProp, R_ls) ∗
      ((C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗ HbThreadIdInv C tp ∗
        ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
        ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
        (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        ((tp - 0xa4#64) ↦₃₂ e0) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
        HbAltstackInv4k C S (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
        HbAltstackMappedPre (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
        HbCallerFrames C sl.sp0 ∗ stackAt (sl.sp0 - 0x170#64) 0x200 ∗ R_cm) :=
    Satisfies.mono (by dsimp only [tp]; sep_entail) hm_m0
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_m1; obtain ⟨R_ls, hm_m2⟩ := hm_m1
  have hm_m3 : s_main.mem ⊨ (C.std.haveLseAtomicsAddr ↦₈ haveLse) ∗
      (R_ls ∗ HbThreadIdInv C tp ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
        ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
        (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        ((tp - 0xa4#64) ↦₃₂ e0) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
        HbAltstackInv4k C S (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
        HbAltstackMappedPre (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
        HbCallerFrames C sl.sp0 ∗ stackAt (sl.sp0 - 0x170#64) 0x200 ∗ R_cm) :=
    Satisfies.mono (by sep_entail) hm_m2
  have hm_lse := Satisfies.of_bupd_frame_left
    (pointsTo8_freeze_ro C.std.haveLseAtomicsAddr haveLse) hm_m3
  rw [← pointsTo8RO_dup C.std.haveLseAtomicsAddr haveLse] at hm_lse
  let R_keep : SepProp :=
    (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    HbThreadIdInv C tp ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
    HbAltstackInv4k C S (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
    HbAltstackMappedPre (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
    HbCallerFrames C sl.sp0 ∗
    (memRegion (sl.sp0 - 524288#64) 523408 ∗ stackAt (sl.sp0 - 0x170#64) 0x200) ∗
    hbRodata C.hbPl ∗ HbCliRoData C ∗ ((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 3#32) ∗
    (C.std.stdoutGlobalAddr ↦ₛ List.replicate 56 0#8) ∗ HbStdinUninit C ∗
    (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ HbPostMainGlobalsNoPs C S ∗ R_ls ∗ R_st12
  have hSat_heap : s_main.mem ⊨ MallocngInitialBss C.mallocng ∗
      (C.mallocng.roTablesAddr ↦ᵣ ProofLib.mallocngRoTablesBytes) ∗
      ((C.std.libcAddr + 3#64) ↦₈ 0#8) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ sl.auxvTableAddr) ∗
      ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
      (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
      (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗ ((tp - 0xa4#64) ↦₃₂ e0) ∗ R_keep :=
    Satisfies.mono (by dsimp only [R_cm, HbUserMainGlobalsPre, R_keep]; sep_entail) hm_lse
  obtain ⟨γ, e_init, hm_heap⟩ := hbStartup_initHeap_at_main hv hS hm hpl hvalid hbudget hinfo
    hbMap htls_cm.2.2.2.2.2.2 htp_m hphys_m hbrk_m hbrkS_m hperm_m hSat_heap
  refine ⟨s0, s_main, altBase, γ, e_init, hload, hcode0, hsteps_all, hmainState,
    hb4k, hbAl, hbFit, hnonull, hbnd_req, ?_⟩
  dsimp only [R_keep, tp, sl] at hm_heap ⊢
  rw [hbStack_main_split (StackLayout.of img inputs).sp0, ← hsp_m, ← htp_m] at hm_heap
  refine Satisfies.mono ?_ hm_heap; dsimp only [HbPostMainGlobalsNoPs, HbPostMainGlobals, M]
  refine Entails.trans (Q :=
    (((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 3#32) ∗
      (C.std.stdoutGlobalAddr ↦ₛ List.replicate 56 0#8)) ∗
    ((sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes.take 8) ∗ R_ls ∗ R_st12) ∗
    ((hbRodata C.hbPl ∗ (hbMallocngIface hpl hbudget.1).Heap γ 0 0 s_main ∗
      HbStdinUninit C ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
      HbCliRoData C ∗ (muslErrnoAddr s_main ↦₃₂ e_init) ∗
      HbThreadIdInv C s_main.tpidrEl0 ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      stackAt s_main.sp 261984) ∗
     ((C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
      HbCallerFrames C sl.sp0 ∗
      ((C.std.cleanupOnceAddr ↦₃₂ 3#32) ∗
        StdVtableRo C.std.cleanupVtableAddr C.std.cleanupVtableShimAddr C.std.cleanupClosureAddr ∗
        StdVtableRo C.std.stdoutVtableAddr C.std.stdoutVtableShimAddr C.std.stdoutCleanupClosureAddr ∗
        (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ (C.std.exitingThreadIdAddr ↦₆₄ 0#64) ∗
        HbMuslExitGlobalsNoNeedLocks C S 0#8) ∗
      HbAltstackInv4k C S (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
      HbAltstackMappedPre (some (altBase, hbExpectedAltRawSz sl.auxvEntries)) ∗
      HbAuxvTicket γ sl.auxvTableAddr sl.auxvEntries ∗ stackAt (s_main.sp - 261984#64) 261936)))
    (by sep_entail) ?_
  refine Entails.trans (sepConj_mono
    (HbStdoutInv_init C (hbMallocngIface hpl hbudget.1).toMallocngCoreIface γ)
    (sepConj_mono_left (Entails.sepExists_right (Q := fun R_unused : SepProp => R_unused)
      _ (Entails.refl _)))) ?_
  sep_entail

end CaseStudies.Hashbrown.Proofs.StdCli
