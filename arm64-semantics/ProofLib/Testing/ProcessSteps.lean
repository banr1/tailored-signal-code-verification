/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.SepLogic.WP.Syscalls
public import ProofLib.SepLogic.WP.SyscallsMmap
public import ProofLib.StdStartup.StackInit

/-!
# Process-Level `SepWP` Step Lemma Tests

Positive and negative (`#guard_msgs`) tests for EL0 system-register accesses, LSE and LL/SC
atomics, process-startup/termination/memory syscalls (`set_tid_address`, `ppoll`, `rt_sigaction`,
`sigaltstack`, `brk`, `mmap`, `exit_group`), `ProcessFieldsPreserved`, and pure-code subroutine
lifting.
-/

set_option autoImplicit false

@[expose] public section

namespace Testing.ProcessSteps

open Arm64 ProofLib

/-! ## EL0 system-register step lemmas -/

theorem test_step_mrs_dczid_el0 {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.sysReg true 0x5807#15 .x5))
    (hnext : SepWP prog target_pc ((s.writeReg64 .x5 4#64).setPC (pc + 4#64)) P post) :
    SepWP prog target_pc s P post :=
  SepWP.step_mrs_dczid_el0 hpc hrun hfetch rfl hnext

theorem test_step_mrs_tpidr_el0 {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.sysReg true 0x5e82#15 .x1))
    (hnext : SepWP prog target_pc ((s.writeReg64 .x1 s.tpidrEl0).setPC (pc + 4#64)) P post) :
    SepWP prog target_pc s P post :=
  SepWP.step_mrs_tpidr_el0 hpc hrun hfetch rfl hnext

theorem test_step_msr_tpidr_el0 {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.sysReg false 0x5e82#15 .x0))
    (hnext : SepWP prog target_pc ((setTpidrEl0 s (s.readReg64 .x0)).setPC (pc + 4#64)) P post) :
    SepWP prog target_pc s P post :=
  SepWP.step_msr_tpidr_el0 hpc hrun hfetch rfl hnext

/-! ## LSE atomics and LL/SC CAS retry step lemmas -/

theorem test_step_cas32 {prog : Program} {target_pc pc ea : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {v0 exp new : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.cas .W32 true true .x0 .x2 .x1))
    (haddr : s.readReg64 .x2 = ea) (halign : MemWidth.isAligned .W32 ea = true)
    (hexp : s.readReg32 .x0 = exp) (hnew : s.readReg32 .x1 = new)
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (((s.writeReg32 .x0 v0).setPC (pc + 4#64)).setMem m')
        ((ea ↦₃₂ (if v0 == exp then new else v0)) ∗ F) post) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post :=
  SepWP.step_cas32 hpc hrun hfetch rfl haddr halign hexp hnew rfl hnext

theorem test_step_cas64 {prog : Program} {target_pc pc ea v0 exp new : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.cas .X64 true true .x0 .x2 .x1))
    (haddr : s.readReg64 .x2 = ea) (halign : MemWidth.isAligned .X64 ea = true)
    (hexp : s.readReg64 .x0 = exp) (hnew : s.readReg64 .x1 = new)
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (((s.writeReg64 .x0 v0).setPC (pc + 4#64)).setMem m')
        ((ea ↦₆₄ (if v0 == exp then new else v0)) ∗ F) post) :
    SepWP prog target_pc s ((ea ↦₆₄ v0) ∗ F) post :=
  SepWP.step_cas64 hpc hrun hfetch rfl haddr halign hexp hnew rfl hnext

theorem test_step_atomicRmw_swp32 {prog : Program} {target_pc pc ea : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {v0 new : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.atomicRmw .SWP .W32 true true .x1 .x2 .x0))
    (haddr : s.readReg64 .x2 = ea) (halign : MemWidth.isAligned .W32 ea = true)
    (hnew : s.readReg32 .x1 = new)
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (((s.writeReg32 .x0 v0).setPC (pc + 4#64)).setMem m')
        ((ea ↦₃₂ new) ∗ F) post) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post :=
  SepWP.step_atomicRmw_swp32 hpc hrun hfetch rfl haddr halign hnew rfl hnext

theorem test_step_cas_llsc_retry32 {prog : Program} {target_pc pc ea : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {v0 exp new : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hf0 : prog.fetch pc = some (.ldxr .W32 true .x2 .x0))
    (hf1 : prog.fetch (pc + 4#64) = some (.addSubShift .W32 .SUBS .xzr .x0 .x16 .LSL 0))
    (hf2 : prog.fetch (pc + 8#64) = some (.bCond .NE 12#64))
    (hf3 : prog.fetch (pc + 12#64) = some (.stxr .W32 false .x17 .x2 .x1))
    (hf4 : prog.fetch (pc + 16#64) = some (.cbz .W32 true .x17 (-16#64)))
    (haddr : s.readReg64 .x2 = ea) (halign : MemWidth.isAligned .W32 ea = true)
    (hexp : s.readReg32 .x16 = exp) (hnew : s.readReg32 .x1 = new)
    (hnext : ∀ m' : Memory,
      let s_cmp := (s.writeReg32 .x0 v0).setPState (subsPState32 v0 exp)
      let s' := if v0 == exp then (s_cmp.stepExclLoop.writeReg32 .x17 0#32).setPC (pc + 20#64)
                else s_cmp.setPC (pc + 20#64)
      SepWP prog target_pc (s'.setMem m') ((ea ↦₃₂ (if v0 == exp then new else v0)) ∗ F) post) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post :=
  SepWP.step_cas_llsc_retry32 hpc hrun hf0 hf1 hf2 hf3 hf4 (by decide) rfl haddr halign hexp hnew
    rfl hnext

theorem test_step_cas_llsc_retry64 {prog : Program} {target_pc pc ea v0 exp new : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hf0 : prog.fetch pc = some (.ldxr .X64 true .x2 .x0))
    (hf1 : prog.fetch (pc + 4#64) = some (.addSubShift .W64 .SUBS .xzr .x0 .x16 .LSL 0))
    (hf2 : prog.fetch (pc + 8#64) = some (.bCond .NE 12#64))
    (hf3 : prog.fetch (pc + 12#64) = some (.stxr .X64 false .x17 .x2 .x1))
    (hf4 : prog.fetch (pc + 16#64) = some (.cbz .W32 true .x17 (-16#64)))
    (haddr : s.readReg64 .x2 = ea) (halign : MemWidth.isAligned .X64 ea = true)
    (hexp : s.readReg64 .x16 = exp) (hnew : s.readReg64 .x1 = new)
    (hnext : ∀ m' : Memory,
      let s_cmp := (s.writeReg64 .x0 v0).setPState (subsPState64 v0 exp)
      let s' := if v0 == exp then (s_cmp.stepExclLoop.writeReg32 .x17 0#32).setPC (pc + 20#64)
                else s_cmp.setPC (pc + 20#64)
      SepWP prog target_pc (s'.setMem m') ((ea ↦₆₄ (if v0 == exp then new else v0)) ∗ F) post) :
    SepWP prog target_pc s ((ea ↦₆₄ v0) ∗ F) post :=
  SepWP.step_cas_llsc_retry64 hpc hrun hf0 hf1 hf2 hf3 hf4 (by decide) rfl haddr halign hexp hnew
    rfl hnext

-- Negative: unaligned 32-bit address (`0x2001`) is rejected by `SepWP.step_cas32`.
/--
error: Tactic `decide` proved that the proposition
-/
#guard_msgs (error, drop info, substring := true) in
example {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {v0 exp new : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.cas .W32 true true .x0 .x2 .x1))
    (haddr : s.readReg64 .x2 = 0x2001#64)
    (hexp : s.readReg32 .x0 = exp) (hnew : s.readReg32 .x1 = new)
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (((s.writeReg32 .x0 v0).setPC (pc + 4#64)).setMem m')
        ((0x2001#64 ↦₃₂ (if v0 == exp then new else v0)) ∗ F) post) :
    SepWP prog target_pc s ((0x2001#64 ↦₃₂ v0) ∗ F) post :=
  SepWP.step_cas32 hpc hrun hfetch rfl haddr (by decide) hexp hnew rfl hnext

-- Negative: aliasing `rs = rt_ld = .x17` in the LL/SC loop is rejected by `hregs`.
/--
error: Tactic `decide` proved that the proposition
-/
#guard_msgs (error, drop info, substring := true) in
example {prog : Program} {target_pc pc ea : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {v0 exp new : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hf0 : prog.fetch pc = some (.ldxr .W32 true .x2 .x17))
    (hf1 : prog.fetch (pc + 4#64) = some (.addSubShift .W32 .SUBS .xzr .x17 .x16 .LSL 0))
    (hf2 : prog.fetch (pc + 8#64) = some (.bCond .NE 12#64))
    (hf3 : prog.fetch (pc + 12#64) = some (.stxr .W32 false .x17 .x2 .x1))
    (hf4 : prog.fetch (pc + 16#64) = some (.cbz .W32 true .x17 (-16#64)))
    (haddr : s.readReg64 .x2 = ea) (halign : MemWidth.isAligned .W32 ea = true)
    (hexp : s.readReg32 .x16 = exp) (hnew : s.readReg32 .x1 = new)
    (hnext : ∀ m' : Memory,
      let s_cmp := (s.writeReg32 .x17 v0).setPState (subsPState32 v0 exp)
      let s' := if v0 == exp then (s_cmp.stepExclLoop.writeReg32 .x17 0#32).setPC (pc + 20#64)
                else s_cmp.setPC (pc + 20#64)
      SepWP prog target_pc (s'.setMem m') ((ea ↦₃₂ (if v0 == exp then new else v0)) ∗ F) post) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post :=
  SepWP.step_cas_llsc_retry32 hpc hrun hf0 hf1 hf2 hf3 hf4 (by decide) rfl haddr halign hexp hnew
    rfl hnext

/-! ## Process-startup and exit syscall step lemmas -/

theorem test_step_svc_set_tid_address {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 96#64)
    (hsvc : prog.evalInst (.system false 0#16) s = execSetTidAddress s)
    (hnext : SepWP prog target_pc ((s.writeReg64 .x0 SIM_TID).setPC (pc + 4#64)) P post) :
    SepWP prog target_pc s P post :=
  SepWP.step_svc_set_tid_address hpc hrun hfetch hx8 rfl hnext hsvc

theorem test_evalPpollBytes_closed_fd0 {fs : FsState} (hfd0 : fs.fds 0#64 = none) :
    evalPpollBytes fs [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0xff#8, 0xff#8] 0 =
      some ([0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0x20#8, 0#8], 1) := by
  dsimp [evalPpollBytes]
  rw [hfd0]

theorem test_evalPpollBytes_rejects_nonstdio (fs : FsState) :
    evalPpollBytes fs [3#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] 0 = none :=
  rfl

theorem test_step_svc_ppoll {prog : Program} {target_pc pc ufds tsp : BitVec 64}
    {s : State} {nfds count : Nat} {bs₀ bs' : List (BitVec 8)} {F : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 73#64)
    (hufds : s.readReg64 .x0 = ufds) (hnfds : (s.readReg32 .x1).toNat = nfds)
    (htsp : s.readReg64 .x2 = tsp) (hsigmask : s.readReg64 .x3 = 0#64)
    (htspNe : tsp ≠ 0#64) (htspFit : tsp.toNat + 16 ≤ 2 ^ 64)
    (hnfdsMax : nfds ≤ FsState.maxOpenFds) (hufdsFit : ufds.toNat + nfds * 8 ≤ 2 ^ 64)
    (hlen : bs₀.length = nfds * 8)
    (heval : evalPpollBytes s.fs bs₀ 0 = some (bs', count))
    (hsvc : prog.evalInst (.system false 0#16) s = execPpoll s)
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (((s.setMem m').writeReg64 .x0 (BitVec.ofNat 64 count)).setPC (pc + 4#64))
        ((ufds ↦ₛ bs') ∗ (((tsp ↦₆₄ 0#64) ∗ ((tsp + 8#64) ↦₆₄ 0#64)) ∗ F)) post) :
    SepWP prog target_pc s
      ((ufds ↦ₛ bs₀) ∗ (((tsp ↦₆₄ 0#64) ∗ ((tsp + 8#64) ↦₆₄ 0#64)) ∗ F)) post :=
  SepWP.step_svc_ppoll hpc hrun hfetch hx8 hufds hnfds htsp hsigmask htspNe htspFit
    hnfdsMax hufdsFit hlen heval hnext hsvc

theorem test_step_svc_rt_sigaction_sigpipe_ign {prog : Program} {target_pc pc act : BitVec 64}
    {s : State} {flags restorer mask : BitVec 64} {F : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 134#64)
    (hsig : s.readReg32 .x0 = 13#32) (hact : s.readReg64 .x1 = act)
    (hold : s.readReg64 .x2 = 0#64) (hsigset : s.readReg64 .x3 = 8#64)
    (hfit : act.toNat + 32 ≤ 2 ^ 64)
    (hsvc : prog.evalInst (.system false 0#16) s = execRtSigaction s)
    (hnext : ∀ m' : Memory,
      let oldAction := s.getSigAction 13#32
      let s₁ := if act == 0#64 then s else s.setSigAction 13#32
        { handler := SIG_IGN, flags := flags &&& UAPI_SA_FLAGS, restorer, mask := mask &&& ~~~SIG_UNBLOCKABLE_MASK }
      SepWP prog target_pc (((s₁.setMem m').writeReg64 .x0 0#64).setPC (pc + 4#64))
        (kSigActionAt act SIG_IGN flags restorer mask ∗
          (optOldSigActionAt 0#64 oldAction.toBytes ∗ F)) post) :
    SepWP prog target_pc s
      (kSigActionAt act SIG_IGN flags restorer mask ∗ (optOldSigActionAt 0#64 [] ∗ F)) post :=
  SepWP.step_svc_rt_sigaction hpc hrun hfetch hx8 hsig hact hold hsigset
    (by decide) (by decide)
    (Or.inr ⟨by decide, by decide, hfit, Or.inr rfl⟩)
    (Or.inl rfl) hnext hsvc

theorem test_step_exit_group_exitsWith {s : State} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = 94#64)
    (hfetch : Program.pureMem.fetchMem s.mem pc = some (.system false 0#16)) :
    Process.ProcessExitsWith Program.pureMem s
      (Process.ProcessOutcome.ofState (s.readReg64 .x0) s) :=
  step_exit_group_exitsWith hpc hrun hx8 hfetch

-- Negative: wrong syscall number (`X8 = 94` instead of `96`) is rejected by `step_svc_set_tid_address`.
/--
error: Application type mismatch
-/
#guard_msgs (error, drop info, substring := true) in
example {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 94#64)
    (hsvc : prog.evalInst (.system false 0#16) s = execSetTidAddress s)
    (hnext : SepWP prog target_pc ((s.writeReg64 .x0 SIM_TID).setPC (pc + 4#64)) P post) :
    SepWP prog target_pc s P post :=
  SepWP.step_svc_set_tid_address hpc hrun hfetch hx8 rfl hnext hsvc

/-! ## `ProcessFieldsPreserved` and pure-code subroutine lifting -/

theorem test_execInst_preserves_processFields_mrs_tpidr (s : State) :
    ProcessFieldsPreserved s (execInst (.sysReg true 0x5e82#15 .x1) s) :=
  execInst_preserves_processFields rfl rfl s

/-- Pure two-instruction fixture: `add x0, x0, #1; ret`. -/
abbrev incWords : List (BitVec 32) := [0x91000400#32, 0xd65f03c0#32]

/-- Pure register contract incrementing `X0`. -/
abbrev incSpec : Spec (BitVec 64) where
  pre := fun v s => ⌜s.readReg64 .x0 = v⌝
  post := fun v _ sf => ⌜sf.readReg64 .x0 = v + 1#64⌝

theorem test_subroutine_ok_lift_pureWords_process {P : Program} {addr : BitVec 64}
    (h_sub : subroutine_ok (Process.pureWordsProg addr incWords) addr incSpec)
    (h_words : P.hasWords addr incWords)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr
      { incSpec with post := fun x s0 sf => ⌜ProcessFieldsPreserved s0 sf⌝ ∗ incSpec.post x s0 sf } :=
  subroutine_ok_lift_pureWords_process h_sub
    (by change (Process.pureWordsProg 0#64 incWords).allInstrs _ = true; decide) h_words h_no_ext
    (h_pre_mem := fun _ _ _ => rfl) (h_post_mem := fun _ _ _ _ _ => rfl)

-- Negative: `SVC #0` (`0xd4000001`) fails the opcode-exclusion precondition of `subroutine_ok_lift_pureWords_process`.
/--
error: Tactic `decide` proved that the proposition
-/
#guard_msgs (error, drop info, substring := true) in
example {P : Program} {addr : BitVec 64}
    (h_sub : subroutine_ok (Process.pureWordsProg addr [0xd4000001#32, 0xd65f03c0#32]) addr incSpec)
    (h_words : P.hasWords addr [0xd4000001#32, 0xd65f03c0#32])
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr
      { incSpec with post := fun x s0 sf => ⌜ProcessFieldsPreserved s0 sf⌝ ∗ incSpec.post x s0 sf } :=
  subroutine_ok_lift_pureWords_process h_sub
    (by change (Process.pureWordsProg 0#64 [0xd4000001#32, 0xd65f03c0#32]).allInstrs _ = true; decide)
    h_words h_no_ext (h_pre_mem := fun _ _ _ => rfl) (h_post_mem := fun _ _ _ _ _ => rfl)

-- Negative: `MSR TPIDR_EL0, X0` (`0xd51bd040`) fails the opcode-exclusion precondition of `subroutine_ok_lift_pureWords_process`.
/--
error: Tactic `decide` proved that the proposition
-/
#guard_msgs (error, drop info, substring := true) in
example {P : Program} {addr : BitVec 64}
    (h_sub : subroutine_ok (Process.pureWordsProg addr [0xd51bd040#32, 0xd65f03c0#32]) addr incSpec)
    (h_words : P.hasWords addr [0xd51bd040#32, 0xd65f03c0#32])
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr
      { incSpec with post := fun x s0 sf => ⌜ProcessFieldsPreserved s0 sf⌝ ∗ incSpec.post x s0 sf } :=
  subroutine_ok_lift_pureWords_process h_sub
    (by change (Process.pureWordsProg 0#64 [0xd51bd040#32, 0xd65f03c0#32]).allInstrs _ = true; decide)
    h_words h_no_ext (h_pre_mem := fun _ _ _ => rfl) (h_post_mem := fun _ _ _ _ _ => rfl)

/-! ## `STLR`/`LDAR`, `brk` page growth, and `stripS` -/

theorem test_step_stlr64 {prog : Program} {target_pc pc ea val v0 : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldarStlr .X64 false .x0 .x1))
    (haddr : s.readReg64 .x0 = ea) (halign : MemWidth.isAligned .X64 ea = true)
    (hval : s.readReg64 .x1 = val)
    (hnext : SepWP prog target_pc ((s.setMem (s.mem.write64 ea val)).setPC (pc + 4#64))
      ((ea ↦₆₄ val) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₆₄ v0) ∗ F) post oom :=
  SepWP.step_stlr64 hpc hrun hfetch rfl haddr halign hval (SepStore64.left (SepStore64.here rfl))
    rfl hnext

theorem test_step_stlr32 {prog : Program} {target_pc pc ea : BitVec 64} {v v0 : BitVec 32}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldarStlr .W32 false .x0 .x1))
    (haddr : s.readReg64 .x0 = ea) (halign : MemWidth.isAligned .W32 ea = true)
    (hval : (s.readReg64 .x1).truncate 32 = v)
    (hnext : ∀ m' : Memory, SepWP prog target_pc ((s.setMem m').setPC (pc + 4#64))
      ((ea ↦₃₂ v) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post oom :=
  SepWP.step_stlr32 hpc hrun hfetch rfl haddr halign hval (SepStore32.left (SepStore32.here rfl))
    rfl hnext

-- Negative: passing a 64-bit `STLR Xt, [Xn]` fetch to `SepWP.step_stlr32` is rejected.
/--
error: Application type mismatch
-/
#guard_msgs (error, drop info, substring := true) in
example {prog : Program} {target_pc pc ea : BitVec 64} {v v0 : BitVec 32}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldarStlr .X64 false .x0 .x1))
    (haddr : s.readReg64 .x0 = ea) (halign : MemWidth.isAligned .W32 ea = true)
    (hval : (s.readReg64 .x1).truncate 32 = v)
    (hnext : ∀ m' : Memory, SepWP prog target_pc ((s.setMem m').setPC (pc + 4#64))
      ((ea ↦₃₂ v) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post oom :=
  SepWP.step_stlr32 hpc hrun hfetch rfl haddr halign hval (SepStore32.left (SepStore32.here rfl))
    rfl hnext

theorem test_step_ldar64 {prog : Program} {target_pc pc ea v : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldarStlr .X64 true .x0 .x1))
    (haddr : s.readReg64 .x0 = ea) (halign : MemWidth.isAligned .X64 ea = true)
    (hnext : SepWP prog target_pc ((s.writeReg .W64 .x1 v).setPC (pc + 4#64))
      ((ea ↦₆₄ v) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₆₄ v) ∗ F) post oom :=
  SepWP.step_ldar64 hpc hrun hfetch rfl haddr halign (SepLoad64.left (SepLoad64.here rfl)) rfl hnext

-- Negative: passing a 32-bit `STLR Wt, [Xn]` fetch to `SepWP.step_stlr64` is rejected.
/--
error: Application type mismatch
-/
#guard_msgs (error, drop info, substring := true) in
example {prog : Program} {target_pc pc ea val v0 : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldarStlr .W32 false .x0 .x1))
    (haddr : s.readReg64 .x0 = ea) (halign : MemWidth.isAligned .X64 ea = true)
    (hval : s.readReg64 .x1 = val)
    (hnext : SepWP prog target_pc ((s.setMem (s.mem.write64 ea val)).setPC (pc + 4#64))
      ((ea ↦₆₄ val) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₆₄ v0) ∗ F) post oom :=
  SepWP.step_stlr64 hpc hrun hfetch rfl haddr halign hval (SepStore64.left (SepStore64.here rfl))
    rfl hnext

theorem test_step_svc_brk_grow_page {prog : Program} {target_pc pc oldBrk : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx0 : s.readReg64 .x0 = oldBrk + 16#64) (hbrk : s.brk = oldBrk)
    (hdvd : 4096 ∣ oldBrk.toNat) (hfit : oldBrk.toNat + (4096 + BRK_GUARD_GAP) ≤ 2 ^ 48)
    (hstart : s.brkStart.ule (oldBrk + 16#64) = true)
    (hmap : s.mem.canMap oldBrk (4096 + BRK_GUARD_GAP) = true)
    (hphys : 4096 ≤ s.physMemAvail)
    (hsvc : prog.evalInst (.system false 0#16) s = execBrk s)
    (hnext : SepWP prog target_pc
      (((((s.setBrk (oldBrk + 16#64)).setMem (s.mem.mapZero oldBrk 4096)).setPhysMemAvail
        (s.physMemAvail - 4096)).writeReg64
        .x0 (oldBrk + 16#64)).setPC (pc + 4#64))
      (memRegion oldBrk 4096 ∗ P) post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_svc_brk_grow_page hpc hrun hfetch hx0 hbrk (by decide) (by decide)
    hdvd hfit hstart hmap hphys hsvc hnext

-- Negative: zero increment (`c = 0#64`) is rejected by `step_svc_brk_grow_page`.
/--
error: Tactic `decide` proved that the proposition
-/
#guard_msgs (error, drop info, substring := true) in
example {prog : Program} {target_pc pc oldBrk : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx0 : s.readReg64 .x0 = oldBrk + 0#64) (hbrk : s.brk = oldBrk)
    (hdvd : 4096 ∣ oldBrk.toNat) (hfit : oldBrk.toNat + (4096 + BRK_GUARD_GAP) ≤ 2 ^ 48)
    (hstart : s.brkStart.ule (oldBrk + 0#64) = true)
    (hmap : s.mem.canMap oldBrk (4096 + BRK_GUARD_GAP) = true)
    (hphys : 4096 ≤ s.physMemAvail)
    (hsvc : prog.evalInst (.system false 0#16) s = execBrk s)
    (hnext : SepWP prog target_pc
      (((((s.setBrk (oldBrk + 0#64)).setMem (s.mem.mapZero oldBrk 4096)).setPhysMemAvail
        (s.physMemAvail - 4096)).writeReg64
        .x0 (oldBrk + 0#64)).setPC (pc + 4#64))
      (memRegion oldBrk 4096 ∗ P) post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_svc_brk_grow_page hpc hrun hfetch hx0 hbrk (by decide) (by decide)
    hdvd hfit hstart hmap hphys hsvc hnext

theorem test_execInst_stripS_and_nonSyscallPreserved (keep : BitVec 64 → Bool) (s : State) :
    execInst (.addSubImm .W64 .ADD .x0 .x0 1#12 false) (stripS keep s) =
      stripS keep (execInst (.addSubImm .W64 .ADD .x0 .x0 1#12 false) s) ∧
    ProofLib.NonSyscallPreserved s (execInst (.addSubImm .W64 .ADD .x0 .x0 1#12 false) s) :=
  ⟨execInst_stripS rfl keep s, ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 rfl s⟩

theorem test_noSvc0Window_pos :
    ProofLib.noSvc0Window [0x00#8, 0x04#8, 0x00#8, 0x91#8, 0xc0#8, 0x03#8, 0x5f#8, 0xd6#8] = true := by
  decide

-- Negative: a 4-byte window containing `SVC #0` (`0xd4000001` LE = `[0x01, 0x00, 0x00, 0xd4]`) is rejected by `noSvc0Window`.
/--
error: Tactic `decide` proved that the proposition
-/
#guard_msgs (error, drop info, substring := true) in
example : ProofLib.noSvc0Window [0x01#8, 0x00#8, 0x00#8, 0xd4#8] = true := by
  decide

theorem test_unmapped_below_stackBaseMin {img : Process.ElfImage} {inputs : Process.ProcessInputs}
    {s0 : State} (h : StdStartup.InitialStackInfo img inputs s0) {a : BitVec 64}
    (hlo : img.brkStart.toNat ≤ a.toNat) (hhi : a.toNat < Process.STACK_BASE_MIN) :
    s0.mem.perm a = none :=
  h.unmapped_below_stackBaseMin hlo hhi

/-! ## `lift_noSyscalls`, `UnmappedBetween`, `SYS_brk`, `traceStreamBytes`, and `pointsToWords64_focus` -/

theorem test_execInst_mrs_tpidr_el0_and_set_tid_address (s : State) (rt : Reg) :
    execInst (.sysReg true 0x5e82#15 rt) s =
      (s.writeReg64 rt s.tpidrEl0).advancePC ∧
    execSetTidAddress s = (s.writeReg64 .x0 1#64).advancePC ∧
    (ProofLib.NonSyscallPreserved s (setTpidrEl0 s 0x1000#64) ↔
      ProofLib.NonSyscallPreserved s s) :=
  ⟨execInst_mrs_tpidr_el0 rt s, execSetTidAddress_eq s, NonSyscallPreserved_setTpidrEl0 s s 0x1000#64⟩

theorem test_steps_lift_noSyscalls {prog : Program} {sa sf : State}
    (hext : ∀ pc, prog.externAt? pc = none)
    (hsvc : prog.svc = Syscall.standard)
    (hsteps : Steps (prog.withSvc noSyscalls) sa sf)
    (hrun : sf.status = .Running) :
    Steps prog sa sf ∧ ProofLib.NonSyscallPreserved sa sf :=
  steps_lift_noSyscalls hext hsvc hsteps hrun

theorem test_lift_noSyscalls {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (hext : ∀ pc, prog.externAt? pc = none)
    (hsvc : prog.svc = Syscall.standard)
    (hwp : SepWP (prog.withSvc noSyscalls) target_pc s P post) :
    SepWP prog target_pc s P (fun sf Q => ProofLib.NonSyscallPreserved s sf ∧ post sf Q) :=
  SepWP.lift_noSyscalls hext hwp hsvc

theorem test_pageMask_toNat (b : BitVec 64) :
    (b &&& 0xfffffffffffff000#64).toNat = b.toNat / 4096 * 4096 :=
  pageMask_toNat b

theorem test_unmappedBetween_brk_chain {img : Process.ElfImage} {inputs : Process.ProcessInputs}
    {s0 : State} (h : StdStartup.InitialStackInfo img inputs s0)
    {base : BitVec 64} {len : Nat}
    (hlo : img.brkStart.toNat ≤ base.toNat)
    (hhi : base.toNat + len ≤ inputs.init.stackTop.toNat - inputs.init.stackSize)
    (hbnd : base.toNat + len < 2 ^ 64) :
    s0.mem.canMap base len = true ∧
      UnmappedBetween (base.toNat + len)
        (inputs.init.stackTop.toNat - inputs.init.stackSize)
        (s0.mem.mapZero base len) := by
  have hunm : UnmappedBetween img.brkStart.toNat
      (inputs.init.stackTop.toNat - inputs.init.stackSize) s0.mem :=
    UnmappedBetween.of_initialStackInfo h
  exact ⟨hunm.canMap hlo hhi hbnd, hunm.mapZero_above hlo hbnd⟩

theorem test_step_svc_brk_query {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 214#64)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hsvc : prog.evalInst (.system false 0#16) s = execBrk s)
    (hnext : SepWP prog target_pc ((s.writeReg64 .x0 s.brk).setPC (pc + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_svc_brk_query hpc hrun hfetch hx8 hx0 hnext hsvc

theorem test_step_svc_brk_grow {prog : Program} {target_pc pc newBrk : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 214#64)
    (hx0 : s.readReg64 .x0 = newBrk)
    (hne : newBrk ≠ 0#64)
    (hmin : s.brkStart.toNat ≤ s.brk.toNat)
    (hle : s.brk.toNat ≤ newBrk.toNat)
    (hfit : newBrk.toNat + BRK_GUARD_GAP ≤ 2 ^ 48)
    (hcur_al : s.brk.toNat % 4096 = 0)
    (hnew_al : newBrk.toNat % 4096 = 0)
    (hmap : s.mem.canMap s.brk (newBrk.toNat - s.brk.toNat + BRK_GUARD_GAP) = true)
    (hphys : newBrk.toNat - s.brk.toNat ≤ s.physMemAvail)
    (hsvc : prog.evalInst (.system false 0#16) s = execBrk s)
    (hnext :
      let m' := s.mem.mapZero s.brk (newBrk.toNat - s.brk.toNat)
      let s' := ((((s.setBrk newBrk).setMem m').setPhysMemAvail
        (s.physMemAvail - (newBrk.toNat - s.brk.toNat))).writeReg64 .x0 newBrk).setPC (pc + 4#64)
      SepWP prog target_pc s' (memRegion s.brk (newBrk.toNat - s.brk.toNat) ∗ P) post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_svc_brk_grow hpc hrun hfetch hx8 hx0 hne hmin hle hfit hcur_al hnew_al hmap hphys
    hnext hsvc

theorem test_step_svc_brk_grow_bytes {prog : Program} {target_pc pc newBrk : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 214#64)
    (hx0 : s.readReg64 .x0 = newBrk)
    (hne : newBrk ≠ 0#64)
    (hmin : s.brkStart.toNat ≤ s.brk.toNat)
    (hle : s.brk.toNat ≤ newBrk.toNat)
    (hfit : newBrk.toNat + BRK_GUARD_GAP ≤ 2 ^ 48)
    (hcur_al : s.brk.toNat % 4096 = 0)
    (hnew_al : newBrk.toNat % 4096 = 0)
    (hmap : s.mem.canMap s.brk (newBrk.toNat - s.brk.toNat + BRK_GUARD_GAP) = true)
    (hphys : newBrk.toNat - s.brk.toNat ≤ s.physMemAvail)
    (hsvc : prog.evalInst (.system false 0#16) s = execBrk s)
    (hnext :
      let m' := s.mem.mapZero s.brk (newBrk.toNat - s.brk.toNat)
      let s' := ((((s.setBrk newBrk).setMem m').setPhysMemAvail
        (s.physMemAvail - (newBrk.toNat - s.brk.toNat))).writeReg64 .x0 newBrk).setPC (pc + 4#64)
      SepWP prog target_pc s'
        ((s.brk ↦ₛ List.replicate (newBrk.toNat - s.brk.toNat) 0#8) ∗ P) post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_svc_brk_grow_bytes hpc hrun hfetch hx8 hx0 hne hmin hle hfit hcur_al hnew_al hmap
    hphys hnext hsvc

-- Negative: `newBrk = 0#64` (a query argument) is rejected by `step_svc_brk_grow`'s `hne` precondition.
/--
error: Tactic `decide` proved that the proposition
-/
#guard_msgs (error, drop info, substring := true) in
example {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 214#64)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hmin : s.brkStart.toNat ≤ s.brk.toNat)
    (hle : s.brk.toNat ≤ (0#64 : BitVec 64).toNat)
    (hfit : (0#64 : BitVec 64).toNat + BRK_GUARD_GAP ≤ 2 ^ 48)
    (hcur_al : s.brk.toNat % 4096 = 0)
    (hnew_al : (0#64 : BitVec 64).toNat % 4096 = 0)
    (hmap : s.mem.canMap s.brk ((0#64 : BitVec 64).toNat - s.brk.toNat + BRK_GUARD_GAP) = true)
    (hphys : (0#64 : BitVec 64).toNat - s.brk.toNat ≤ s.physMemAvail)
    (hsvc : prog.evalInst (.system false 0#16) s = execBrk s)
    (hnext :
      let m' := s.mem.mapZero s.brk ((0#64 : BitVec 64).toNat - s.brk.toNat)
      let s' := ((((s.setBrk 0#64).setMem m').setPhysMemAvail
        (s.physMemAvail - ((0#64 : BitVec 64).toNat - s.brk.toNat))).writeReg64 .x0 0#64).setPC (pc + 4#64)
      SepWP prog target_pc s'
        (memRegion s.brk ((0#64 : BitVec 64).toNat - s.brk.toNat) ∗ P) post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_svc_brk_grow hpc hrun hfetch hx8 hx0 (by decide) hmin hle hfit hcur_al hnew_al hmap
    hphys hnext hsvc

theorem test_traceStreamBytes_lemmas (t1 t2 : List TraceEvent) (bs : List (BitVec 8)) :
    Process.ProcessOutcome.traceStreamBytes .stdout (t1 ++ t2) =
      Process.ProcessOutcome.traceStreamBytes .stdout t1 ++
        Process.ProcessOutcome.traceStreamBytes .stdout t2 ∧
    Process.ProcessOutcome.traceStreamBytes .stdout (TraceEvent.ofBytes .stdout bs) = bs ∧
    Process.ProcessOutcome.traceStreamBytes .stderr (TraceEvent.ofBytes .stderr bs) = bs ∧
    Process.ProcessOutcome.traceStreamBytes .stderr (TraceEvent.ofBytes .stdout bs) = [] ∧
    Process.ProcessOutcome.traceStreamBytes .stdout
      (TraceEvent.ofBytes (OutputStream.ofFd 3#64) bs) = [] :=
  ⟨traceStreamBytes_append .stdout t1 t2,
   traceStreamBytes_stdout_ofBytes bs,
   traceStreamBytes_stderr_ofBytes bs,
   traceStreamBytes_stderr_ofBytes_stdout bs,
   traceStreamBytes_ofBytes_fd3_stdout bs⟩

theorem test_pointsToWords64_focus (base : BitVec 64) :
    (base ↦₆₄* [1#64, 2#64, 3#64]) =
      (((base + 8#64) ↦₆₄ 2#64) ∗
        (pointsToArray 8 (· ↦₆₄ ·) base [1#64] ∗
          pointsToArray 8 (· ↦₆₄ ·) (base + 16#64) [3#64])) :=
  pointsToWords64_focus base [1#64, 2#64, 3#64] 1 (by decide)

theorem test_pointsToWords64_focus_pair (base : BitVec 64) :
    (base ↦₆₄* [1#64, 2#64, 3#64]) =
      (((base + 8#64) ↦₆₄ 2#64) ∗
        (((base + 8#64) + 8#64) ↦₆₄ 3#64) ∗
        ((base ↦₆₄* [1#64]) ∗
          ((((base + 8#64) + 8#64) + 8#64) ↦₆₄* []))) :=
  pointsToWords64_focus_pair base [1#64, 2#64, 3#64] 1 (by decide)

-- Negative: out-of-bounds word index (`i = 3` on a 3-element word list) is rejected by `pointsToWords64_focus`.
/--
error: Tactic `decide` proved that the proposition
-/
#guard_msgs (error, drop info, substring := true) in
example (base : BitVec 64) :
    (base ↦₆₄* [1#64, 2#64, 3#64]) =
      (((base + BitVec.ofNat 64 (8 * 3)) ↦₆₄ ([1#64, 2#64, 3#64].getD 3 0#64)) ∗
        (pointsToArray 8 (· ↦₆₄ ·) base ([1#64, 2#64, 3#64].take 3) ∗
          pointsToArray 8 (· ↦₆₄ ·) (base + BitVec.ofNat 64 (8 * 4)) ([1#64, 2#64, 3#64].drop 4))) :=
  pointsToWords64_focus base [1#64, 2#64, 3#64] 3 (by decide)

/-! ## `sigaltstack`, `rt_sigaction`, and `mmap` step lemmas -/

theorem test_stackTAt_and_sigAltStack_toBytes (addr ssSp flagsWord ssSize : BitVec 64)
    (sas : SigAltStack) (sp : BitVec 64) (hne : addr ≠ 0#64) :
    (addr ↦ₛ sas.toBytes sp) =
      ((addr ↦₆₄ sas.sp) ∗ ((addr + 8#64) ↦₃₂ sas.flags sp) ∗
       ((addr + 12#64) ↦₃₂ 0#32) ∗ ((addr + 16#64) ↦₆₄ sas.size)) ∧
    ((addr ↦₆₄ ssSp) ∗ ((addr + 8#64) ↦₆₄ flagsWord) ∗ ((addr + 16#64) ↦₆₄ ssSize)) =
      stackTAt addr ssSp (flagsWord.truncate 32) (flagsWord.extractLsb' 32 32) ssSize :=
  ⟨pointsToBytes_sigAltStack_toBytes addr sas sp,
   stackTAt_eq_of_pointsTo64 addr ssSp flagsWord ssSize hne⟩

theorem test_step_svc_sigaltstack_install {prog : Program} {target_pc pc uss ssSp uoss : BitVec 64}
    {pad : BitVec 32} {oldBs₀ : List (BitVec 8)} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 132#64)
    (huss : s.readReg64 .x0 = uss) (huoss : s.readReg64 .x1 = uoss)
    (hussFit : uss.toNat + 24 ≤ 2 ^ 64)
    (hon : s.sigAltStack.onSigStack s.sp = false)
    (huossOk : uoss = 0#64 ∨ (uoss.toNat + 24 ≤ 2 ^ 64 ∧ oldBs₀.length = 24))
    (hsvc : prog.evalInst (.system false 0#16) s = execSigaltstack s)
    (hnext : ∀ m' : Memory,
      let oldBytes := s.sigAltStack.toBytes s.sp
      let s₁ :=
        if uss == 0#64 then s
        else if (0#32 &&& ~~~SS_AUTODISARM) == SS_DISABLE then
          s.setSigAltStack { sp := 0#64, size := 0#64, ssFlags := 0#32 }
        else
          s.setSigAltStack { sp := ssSp, size := 0x41000#64, ssFlags := 0#32 }
      SepWP prog target_pc (((s₁.setMem m').writeReg64 .x0 0#64).setPC (pc + 4#64))
        (stackTAt uss ssSp 0#32 pad 0x41000#64 ∗ (optOldStackTAt uoss oldBytes ∗ F)) post oom) :
    SepWP prog target_pc s
      (stackTAt uss ssSp 0#32 pad 0x41000#64 ∗ (optOldStackTAt uoss oldBs₀ ∗ F)) post oom :=
  SepWP.step_svc_sigaltstack hpc hrun hfetch hx8 huss huoss
    (Or.inr ⟨hussFit, hon, Or.inr ⟨Or.inl (by decide), by decide⟩⟩) huossOk hnext hsvc

theorem test_step_svc_sigaltstack_disable_nonzero_size {prog : Program}
    {target_pc pc uss ssSp ssSize : BitVec 64} {pad : BitVec 32}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 132#64)
    (huss : s.readReg64 .x0 = uss) (huoss : s.readReg64 .x1 = 0#64)
    (hussFit : uss.toNat + 24 ≤ 2 ^ 64)
    (hon : s.sigAltStack.onSigStack s.sp = false)
    (hsvc : prog.evalInst (.system false 0#16) s = execSigaltstack s)
    (hnext : ∀ m' : Memory,
      let oldBytes := s.sigAltStack.toBytes s.sp
      let s₁ :=
        if uss == 0#64 then s
        else if (SS_DISABLE &&& ~~~SS_AUTODISARM) == SS_DISABLE then
          s.setSigAltStack { sp := 0#64, size := 0#64, ssFlags := SS_DISABLE }
        else
          s.setSigAltStack { sp := ssSp, size := ssSize, ssFlags := SS_DISABLE }
      SepWP prog target_pc (((s₁.setMem m').writeReg64 .x0 0#64).setPC (pc + 4#64))
        (stackTAt uss ssSp SS_DISABLE pad ssSize ∗ (optOldStackTAt 0#64 oldBytes ∗ F)) post oom) :
    SepWP prog target_pc s
      (stackTAt uss ssSp SS_DISABLE pad ssSize ∗ (optOldStackTAt 0#64 [] ∗ F)) post oom :=
  SepWP.step_svc_sigaltstack hpc hrun hfetch hx8 huss huoss
    (Or.inr ⟨hussFit, hon, Or.inl (by decide)⟩) (Or.inl rfl) hnext hsvc

-- Negative: `ssSize = 5119 < MINSIGSTKSZ` (`5120`) without `SS_DISABLE` is rejected by `step_svc_sigaltstack`.
/--
error: Tactic `decide` proved that the proposition
-/
#guard_msgs (error, drop info, substring := true) in
example {prog : Program} {target_pc pc uss ssSp : BitVec 64} {pad : BitVec 32}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 132#64)
    (huss : s.readReg64 .x0 = uss) (huoss : s.readReg64 .x1 = 0#64)
    (hussFit : uss.toNat + 24 ≤ 2 ^ 64)
    (hon : s.sigAltStack.onSigStack s.sp = false)
    (hsvc : prog.evalInst (.system false 0#16) s = execSigaltstack s)
    (hnext : ∀ m' : Memory,
      let oldBytes := s.sigAltStack.toBytes s.sp
      let s₁ :=
        if uss == 0#64 then s
        else if (0#32 &&& ~~~SS_AUTODISARM) == SS_DISABLE then
          s.setSigAltStack { sp := 0#64, size := 0#64, ssFlags := 0#32 }
        else
          s.setSigAltStack { sp := ssSp, size := 5119#64, ssFlags := 0#32 }
      SepWP prog target_pc (((s₁.setMem m').writeReg64 .x0 0#64).setPC (pc + 4#64))
        (stackTAt uss ssSp 0#32 pad 5119#64 ∗ (optOldStackTAt 0#64 oldBytes ∗ F)) post oom) :
    SepWP prog target_pc s
      (stackTAt uss ssSp 0#32 pad 5119#64 ∗ (optOldStackTAt 0#64 [] ∗ F)) post oom :=
  SepWP.step_svc_sigaltstack hpc hrun hfetch hx8 huss huoss
    (Or.inr ⟨hussFit, hon, Or.inr ⟨Or.inl (by decide), by decide⟩⟩) (Or.inl rfl) hnext hsvc

theorem test_step_svc_rt_sigaction_any_segv {prog : Program}
    {target_pc pc act handler flags restorer mask : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 134#64)
    (hsig : s.readReg32 .x0 = 11#32) (hact : s.readReg64 .x1 = act)
    (hold : s.readReg64 .x2 = 0#64) (hsigset : s.readReg64 .x3 = 8#64)
    (hfit : act.toNat + 32 ≤ 2 ^ 64)
    (hsvc : prog.evalInst (.system false 0#16) s = execRtSigaction s)
    (hnext : ∀ m' : Memory,
      let oldAction := s.getSigAction 11#32
      let s₁ := if act == 0#64 then s else s.setSigAction 11#32
        { handler, flags := flags &&& UAPI_SA_FLAGS, restorer, mask := mask &&& ~~~SIG_UNBLOCKABLE_MASK }
      SepWP prog target_pc (((s₁.setMem m').writeReg64 .x0 0#64).setPC (pc + 4#64))
        (kSigActionAt act handler flags restorer mask ∗
          (optOldSigActionAt 0#64 oldAction.toBytes ∗ F)) post oom) :
    SepWP prog target_pc s
      (kSigActionAt act handler flags restorer mask ∗ (optOldSigActionAt 0#64 [] ∗ F)) post oom :=
  SepWP.step_svc_rt_sigaction_any hpc hrun hfetch hx8 hsig hact hold hsigset
    (by decide) (by decide)
    (Or.inr ⟨by decide, by decide, hfit, Or.inr (Or.inr (Or.inl rfl))⟩)
    (Or.inl rfl) hnext hsvc

-- Negative: custom handler (`0x400500#64`) on `SIGTERM` (`15#32`) is rejected by `step_svc_rt_sigaction_any`.
/--
error: Tactic `decide` proved that the proposition
-/
#guard_msgs (error, drop info, substring := true) in
example {prog : Program} {target_pc pc act flags restorer mask : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 134#64)
    (hsig : s.readReg32 .x0 = 15#32) (hact : s.readReg64 .x1 = act)
    (hold : s.readReg64 .x2 = 0#64) (hsigset : s.readReg64 .x3 = 8#64)
    (hfit : act.toNat + 32 ≤ 2 ^ 64)
    (hsvc : prog.evalInst (.system false 0#16) s = execRtSigaction s)
    (hnext : ∀ m' : Memory,
      let oldAction := s.getSigAction 15#32
      let s₁ := if act == 0#64 then s else s.setSigAction 15#32
        { handler := 0x400500#64, flags := flags &&& UAPI_SA_FLAGS, restorer, mask := mask &&& ~~~SIG_UNBLOCKABLE_MASK }
      SepWP prog target_pc (((s₁.setMem m').writeReg64 .x0 0#64).setPC (pc + 4#64))
        (kSigActionAt act 0x400500#64 flags restorer mask ∗
          (optOldSigActionAt 0#64 oldAction.toBytes ∗ F)) post oom) :
    SepWP prog target_pc s
      (kSigActionAt act 0x400500#64 flags restorer mask ∗ (optOldSigActionAt 0#64 [] ∗ F)) post oom :=
  SepWP.step_svc_rt_sigaction_any hpc hrun hfetch hx8 hsig hact hold hsigset
    (by decide) (by decide)
    (Or.inr ⟨by decide, by decide, hfit, by decide⟩)
    (Or.inl rfl) hnext hsvc

theorem test_step_svc_mmap_anon_map_stack_unaligned_len {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64)
    (hprot : s.readReg64 .x2 = 3#64)
    (hflags : s.readReg64 .x3 = 0x20022#64)
    (hoff : s.readReg64 .x5 = 0#64)
    (hlen : (s.readReg64 .x1).toNat = 0x41020)
    (hok : ∀ (mb : BitVec 64) (m' : Memory),
      mb ≠ 0#64 → 4096 ∣ mb.toNat → mb.toNat + pageAlignUp 0x41020 ≤ 2 ^ 48 →
      SepWP prog target_pc
        ((((s.setPhysMemAvail (s.physMemAvail - pageAlignUp 0x41020)).nextOracle.writeReg64 .x0 mb).setPC
          (pc + 4#64)).setMem m')
        ((mb ↦ₛ List.replicate (pageAlignUp 0x41020) 0#8) ∗ P) post oom)
    (hoom : ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R))
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_svc_mmap_anon hpc hrun hfetch hx8 hprot (Or.inr hflags) hoff hlen (by decide)
    hok hoom hsvc

/-! ### Anonymous `mmap` reserve, map, and `MAP_FIXED` commit/decommit -/

theorem test_step_svc_mmap_anon_reserve_two_pages {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64) (hprot : s.readReg64 .x2 = 0#64)
    (hflags : s.readReg64 .x3 = 0x22#64) (hoff : s.readReg64 .x5 = 0#64)
    (hlen : (s.readReg64 .x1).toNat = 0x2000)
    (hok : ∀ (mb : BitVec 64) (m' : Memory),
      MMAP_MIN_ADDR ≤ mb.toNat → mb ≠ 0#64 → 4096 ∣ mb.toNat → mb.toNat + 0x2000 ≤ 2 ^ 48 →
      m' = (s.mem.mapZero mb 0x2000).setPermNonFrozen mb 0x2000 Perm.protNone →
      SepWP prog target_pc
        (((s.nextOracle.writeReg64 .x0 mb).setPC (pc + 4#64)).setMem m')
        ((mb ↦ₙ List.replicate 0x2000 0#8) ∗ memMapped mb 0x2000 ∗ P) post oom)
    (hoom : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx) 0x2000 = none →
      ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R))
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_svc_mmap_anon_reserve hpc hrun hfetch hx8 hprot (Or.inl hflags) hoff
    (by rw [hlen]; decide) (by decide) hok hoom hsvc

/-- An unaligned `X1 = 0x1001` reserves the page-rounded `pageAlignUp 0x1001 = 0x2000` bytes. -/
theorem test_step_svc_mmap_anon_reserve_unaligned_len {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64) (hprot : s.readReg64 .x2 = 0#64)
    (hflags : s.readReg64 .x3 = 0x20022#64) (hoff : s.readReg64 .x5 = 0#64)
    (hlen : (s.readReg64 .x1).toNat = 0x1001)
    (hok : ∀ (mb : BitVec 64) (m' : Memory),
      MMAP_MIN_ADDR ≤ mb.toNat → mb ≠ 0#64 → 4096 ∣ mb.toNat → mb.toNat + 0x2000 ≤ 2 ^ 48 →
      m' = (s.mem.mapZero mb 0x2000).setPermNonFrozen mb 0x2000 Perm.protNone →
      SepWP prog target_pc
        (((s.nextOracle.writeReg64 .x0 mb).setPC (pc + 4#64)).setMem m')
        ((mb ↦ₙ List.replicate 0x2000 0#8) ∗ memMapped mb 0x2000 ∗ P) post oom)
    (hoom : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx) 0x2000 = none →
      ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R))
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_svc_mmap_anon_reserve hpc hrun hfetch hx8 hprot (Or.inr hflags) hoff
    (by rw [hlen]; decide) (by decide) hok hoom hsvc

/-- `hoom` defaults to closing an `allowOom` (`⌜True⌝`) out-of-memory postcondition. -/
theorem test_step_svc_mmap_anon_reserve_allowOom {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64) (hprot : s.readReg64 .x2 = 0#64)
    (hflags : s.readReg64 .x3 = 0x22#64) (hoff : s.readReg64 .x5 = 0#64)
    (hlen : (s.readReg64 .x1).toNat = 0x2000)
    (hok : ∀ (mb : BitVec 64) (m' : Memory),
      MMAP_MIN_ADDR ≤ mb.toNat → mb ≠ 0#64 → 4096 ∣ mb.toNat → mb.toNat + 0x2000 ≤ 2 ^ 48 →
      m' = (s.mem.mapZero mb 0x2000).setPermNonFrozen mb 0x2000 Perm.protNone →
      SepWP prog target_pc
        (((s.nextOracle.writeReg64 .x0 mb).setPC (pc + 4#64)).setMem m')
        ((mb ↦ₙ List.replicate 0x2000 0#8) ∗ memMapped mb 0x2000 ∗ P) post
        (fun _ => ⌜True⌝))
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s) :
    SepWP prog target_pc s P post (fun _ => ⌜True⌝) :=
  SepWP.step_svc_mmap_anon_reserve hpc hrun hfetch hx8 hprot (Or.inl hflags) hoff
    (by rw [hlen]; decide) (by decide) hok (hsvc := hsvc)

theorem test_step_svc_mmap_anon_rw_unaligned_len {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64) (hprot : s.readReg64 .x2 = 3#64)
    (hflags : s.readReg64 .x3 = 0x22#64) (hoff : s.readReg64 .x5 = 0#64)
    (hlen : (s.readReg64 .x1).toNat = 0x1001)
    (hok : ∀ (mb : BitVec 64) (m' : Memory),
      MMAP_MIN_ADDR ≤ mb.toNat → mb ≠ 0#64 → 4096 ∣ mb.toNat → mb.toNat + 0x2000 ≤ 2 ^ 48 →
      0x2000 ≤ s.physMemAvail → m' = s.mem.mapZero mb 0x2000 →
      SepWP prog target_pc
        ((((s.setPhysMemAvail (s.physMemAvail - 0x2000)).nextOracle.writeReg64 .x0 mb).setPC
          (pc + 4#64)).setMem m')
        ((mb ↦ₛ List.replicate 0x2000 0#8) ∗ memMapped mb 0x2000 ∗ P) post oom)
    (hoom : (sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx) 0x2000 = none ∨
        s.physMemAvail < 0x2000) →
      ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R))
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_svc_mmap_anon_rw hpc hrun hfetch hx8 hprot (Or.inl hflags) hoff
    (by rw [hlen]; decide) (by decide) hok hoom hsvc

-- Negative: the page-rounded length of an unaligned `X1 = 0x1001` is `0x2000`, not `0x1001`.
/-- error: Tactic `decide` proved that the proposition
  pageAlignUp 4097 = 4097
is false -/
#guard_msgs (error, drop info, substring := true) in
example {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64) (hprot : s.readReg64 .x2 = 0#64)
    (hflags : s.readReg64 .x3 = 0x22#64) (hoff : s.readReg64 .x5 = 0#64)
    (hlen : (s.readReg64 .x1).toNat = 0x1001)
    (hok : ∀ (mb : BitVec 64) (m' : Memory),
      MMAP_MIN_ADDR ≤ mb.toNat → mb ≠ 0#64 → 4096 ∣ mb.toNat → mb.toNat + 0x1001 ≤ 2 ^ 48 →
      m' = (s.mem.mapZero mb 0x1001).setPermNonFrozen mb 0x1001 Perm.protNone →
      SepWP prog target_pc
        (((s.nextOracle.writeReg64 .x0 mb).setPC (pc + 4#64)).setMem m')
        ((mb ↦ₙ List.replicate 0x1001 0#8) ∗ memMapped mb 0x1001 ∗ P) post
        (fun _ => ⌜True⌝))
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s) :
    SepWP prog target_pc s P post (fun _ => ⌜True⌝) :=
  SepWP.step_svc_mmap_anon_reserve hpc hrun hfetch hx8 hprot (Or.inl hflags) hoff
    (by rw [hlen]; decide) (by decide) hok (hsvc := hsvc)

theorem test_step_svc_mmap_fixed_commit_two_pages {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64) (haddr : s.readReg64 .x0 = 0x10000#64)
    (hprot : s.readReg64 .x2 = 3#64) (hflags : s.readReg64 .x3 = 0x32#64)
    (hoff : s.readReg64 .x5 = 0#64) (hlen : (s.readReg64 .x1).toNat = 0x2000)
    (hok : ∀ m' : Memory, 0x2000 ≤ s.physMemAvail →
      m' = (s.mem.unmapNonFrozen 0x10000#64 0x2000).mapZero 0x10000#64 0x2000 →
      SepWP prog target_pc
        ((((s.setPhysMemAvail (s.physMemAvail - 0x2000)).writeReg64 .x0 0x10000#64).setPC
          (pc + 4#64)).setMem m')
        ((0x10000#64 ↦ₛ List.replicate 0x2000 0#8) ∗ memMapped 0x10000#64 0x2000 ∗ P) post oom)
    (hoom : ∀ R, ¬ 0x2000 ≤ s.physMemAvail →
      (s.mem ⊨ (memRegionProtNone 0x10000#64 0x2000 ∗ memMapped 0x10000#64 0x2000 ∗ P) ∗ R) →
      (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R))
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s) :
    SepWP prog target_pc s
      (memRegionProtNone 0x10000#64 0x2000 ∗ memMapped 0x10000#64 0x2000 ∗ P) post oom :=
  SepWP.step_svc_mmap_fixed_commit hpc hrun hfetch hx8 haddr hprot hflags hoff hlen
    (by decide) (by decide) (by decide) (by decide) (by decide) hok hoom hsvc

theorem test_step_svc_mmap_fixed_decommit_two_pages {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64) (haddr : s.readReg64 .x0 = 0x10000#64)
    (hprot : s.readReg64 .x2 = 0#64) (hflags : s.readReg64 .x3 = 0x32#64)
    (hoff : s.readReg64 .x5 = 0#64) (hlen : (s.readReg64 .x1).toNat = 0x2000)
    (hok : ∀ m' : Memory,
      m' = ((s.mem.unmapNonFrozen 0x10000#64 0x2000).mapZero 0x10000#64 0x2000).setPermNonFrozen
        0x10000#64 0x2000 Perm.protNone →
      SepWP prog target_pc
        ((((s.setPhysMemAvail (s.physMemAvail + 0x2000)).writeReg64 .x0 0x10000#64).setPC
          (pc + 4#64)).setMem m')
        ((0x10000#64 ↦ₙ List.replicate 0x2000 0#8) ∗ P) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s) :
    SepWP prog target_pc s (memRegion 0x10000#64 0x2000 ∗ P) post oom :=
  SepWP.step_svc_mmap_fixed_decommit hpc hrun hfetch hx8 haddr hprot hflags hoff hlen
    (by decide) (by decide) (by decide) (by decide) (by decide) hok hsvc

end Testing.ProcessSteps
