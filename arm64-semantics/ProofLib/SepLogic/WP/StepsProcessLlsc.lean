/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.WP.StepsSubword
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Outline-Atomics LL/SC CAS Retry Step Lemmas

`SepWP` step lemmas (`SepWP.step_cas_llsc_retry32`, `SepWP.step_cas_llsc_retry64`) for the
5-instruction AArch64 outline-atomics LL/SC compare-and-swap retry loop under arbitrary `exclFails`.
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib

open Arm64

private theorem reg_ne_of_bne {r1 r2 : Reg} (h : (r1 != r2) = true) : r1 ≠ r2 := by
  intro heq; subst heq; revert h; cases r1 <;> decide +revert

private theorem readReg64_writeReg_ne (s : State) (w : Width) (r1 r2 : Reg) (v : BitVec 64)
    (h : (r2 != r1) = true) : (s.writeReg w r1 v).readReg64 r2 = s.readReg64 r2 := by
  cases w with
  | W32 => exact State.readReg64_writeReg64_ne s r1 r2 ((v.truncate 32).zeroExtend 64) (reg_ne_of_bne h)
  | W64 => exact State.readReg64_writeReg64_ne s r1 r2 v (reg_ne_of_bne h)

private theorem step_ldxr_cmp_bne {prog : Program} {target_pc : BitVec 64}
    {s0 : State} {Q Qoom : State → Prop} {pc ea v_ld exp64 : BitVec 64}
    {sz : MemWidth} {w_op : Width} {acq : Bool} {rn rt_ld r_exp : Reg} {ps : PState}
    (hw : (match sz with | .X64 => .W64 | _ => .W32 : Width) = w_op)
    (hpc : s0.pc = pc) (hrun : s0.status = .Running)
    (hf0 : prog.fetch pc = some (.ldxr sz acq rn rt_ld))
    (hf1 : prog.fetch (pc + 4#64) = some (.addSubShift w_op .SUBS .xzr rt_ld r_exp .LSL 0))
    (hf2 : prog.fetch (pc + 8#64) = some (.bCond .NE 12#64))
    (hexp_ld : (r_exp != rt_ld) = true)
    (hsp : checkRegSPAligned s0 rn = true) (haddr : s0.readReg64 rn = ea)
    (halign : sz.isAligned ea = true) (hcr : s0.mem.canRead ea sz.bytes = true)
    (hrd : s0.mem.readSized sz false ea = v_ld) (hexp : s0.readReg w_op r_exp = exp64)
    (hps : (evalAddSub w_op .SUBS ((s0.writeReg w_op rt_ld v_ld).readReg w_op rt_ld)
      (shiftVal w_op exp64 .LSL 0) none).2 = some ps)
    (hk : reaches_pc prog target_pc
      (((s0.writeReg w_op rt_ld v_ld).setPState ps).setPC
        (if ConditionHolds .NE ps then pc + 20#64 else pc + 12#64)) Q Qoom) :
    reaches_pc prog target_pc s0 Q Qoom := by
  apply reaches_pc_step hrun (hpc.symm ▸ hf0)
  have hs1 : prog.evalInst (.ldxr sz acq rn rt_ld) s0 =
      (s0.writeReg w_op rt_ld v_ld).setPC (pc + 4#64) := by
    subst hw
    dsimp only [Program.evalInst, execInstWithSvc]
    simp only [hsp, haddr, halign, hcr, hrd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases s0; cases sz <;> cases rt_ld <;> simp [State.writeReg, State.writeReg64,
      State.advancePC, State.setPC, hpc]
  rw [hs1]
  have hrun1 : ((s0.writeReg w_op rt_ld v_ld).setPC (pc + 4#64)).status = .Running := by
    cases s0; cases w_op <;> cases rt_ld <;> exact hrun
  apply reaches_pc_step hrun1 hf1
  have hs2 : prog.evalInst (.addSubShift w_op .SUBS .xzr rt_ld r_exp .LSL 0)
      ((s0.writeReg w_op rt_ld v_ld).setPC (pc + 4#64)) =
      ((s0.writeReg w_op rt_ld v_ld).setPState ps).setPC (pc + 8#64) := by
    have hexp1 : ((s0.writeReg w_op rt_ld v_ld).setPC (pc + 4#64)).readReg w_op r_exp = exp64 := by
      cases w_op <;> {
        dsimp only [State.readReg, State.readReg32]
        rw [State.readReg64_setPC, readReg64_writeReg_ne s0 _ rt_ld r_exp v_ld hexp_ld]
        exact hexp }
    have hld1 : ((s0.writeReg w_op rt_ld v_ld).setPC (pc + 4#64)).readReg w_op rt_ld =
        (s0.writeReg w_op rt_ld v_ld).readReg w_op rt_ld := by cases w_op <;> rfl
    have hp4 : (pc + 4#64) + 4#64 = pc + 8#64 := by bv_omega
    dsimp only [Program.evalInst, execInstWithSvc, execAddSubShift]
    rw [hld1, hexp1, hps]
    cases s0; cases w_op <;> cases rt_ld <;> simp [State.writeReg, State.writeReg64,
      State.setPState, State.advancePC, State.setPC, hp4]
  rw [hs2]
  have hrun2 : (((s0.writeReg w_op rt_ld v_ld).setPState ps).setPC (pc + 8#64)).status = .Running := by
    cases s0; cases w_op <;> cases rt_ld <;> exact hrun
  apply reaches_pc_step hrun2 hf2
  have hs3 : prog.evalInst (.bCond .NE 12#64)
      (((s0.writeReg w_op rt_ld v_ld).setPState ps).setPC (pc + 8#64)) =
      ((s0.writeReg w_op rt_ld v_ld).setPState ps).setPC
        (if ConditionHolds .NE ps then pc + 20#64 else pc + 12#64) := by
    have hp8_12 : (pc + 8#64) + 12#64 = pc + 20#64 := by bv_omega
    have hp8_4 : (pc + 8#64) + 4#64 = pc + 12#64 := by bv_omega
    have hp_ps : (((s0.writeReg w_op rt_ld v_ld).setPState ps).setPC (pc + 8#64)).pstate = ps := by
      cases s0; cases w_op <;> cases rt_ld <;> rfl
    dsimp only [Program.evalInst, execInstWithSvc]
    rw [hp_ps]
    cases ConditionHolds .NE ps <;> cases s0 <;> cases w_op <;> cases rt_ld <;>
      simp [State.writeReg, State.writeReg64, State.setPState, State.advancePC, State.setPC,
        hp8_12, hp8_4]
  rw [hs3]
  exact hk

private theorem reaches_pc_cas_llsc_loop {prog : Program} {target_pc : BitVec 64}
    {s1 : State} {Q Qoom : State → Prop} {pc ea v_ld exp64 : BitVec 64}
    {sz : MemWidth} {w_op : Width} {acq rel : Bool} {rs rn rt rt_ld r_exp : Reg} {ps : PState}
    (hw : (match sz with | .X64 => .W64 | _ => .W32 : Width) = w_op)
    (hpc1 : s1.pc = pc + 12#64) (hrun1 : s1.status = .Running) (hps1 : s1.pstate = ps)
    (hf0 : prog.fetch pc = some (.ldxr sz acq rn rt_ld))
    (hf1 : prog.fetch (pc + 4#64) = some (.addSubShift w_op .SUBS .xzr rt_ld r_exp .LSL 0))
    (hf2 : prog.fetch (pc + 8#64) = some (.bCond .NE 12#64))
    (hf3 : prog.fetch (pc + 12#64) = some (.stxr sz rel rs rn rt))
    (hf4 : prog.fetch (pc + 16#64) = some (.cbz .W32 true rs (-16#64)))
    (hrs : rs.isNonZeroGpr = true) (hrn_s : (rn != rs) = true) (hrt_s : (rt != rs) = true)
    (hld_s : (rt_ld != rs) = true) (hexp_s : (r_exp != rs) = true) (hexp_ld : (r_exp != rt_ld) = true)
    (hsp1 : checkRegSPAligned s1 rn = true) (haddr1 : s1.readReg64 rn = ea)
    (halign : sz.isAligned ea = true)
    (hcr : s1.mem.canRead ea sz.bytes = true) (hcw : s1.mem.canWrite ea sz.bytes = true)
    (hrd : s1.mem.readSized sz false ea = v_ld) (hexp1 : s1.readReg w_op r_exp = exp64)
    (hld_idem : s1.writeReg w_op rt_ld v_ld = s1)
    (hps : (evalAddSub w_op .SUBS (s1.readReg w_op rt_ld) (shiftVal w_op exp64 .LSL 0) none).2 = some ps)
    (hcond : ConditionHolds .NE ps = false)
    (ef : List Bool) (w_rs : BitVec 64)
    (hsucc : reaches_pc prog target_pc
      (((s1.withExclFails (ef.dropWhile (· == true)).tail).writeReg .W32 rs 0#64).setPC (pc + 20#64)
        |>.setMem (s1.mem.writeSized sz ea (s1.readReg64 rt))) Q Qoom) :
    reaches_pc prog target_pc (s1.stxrIter ef rs w_rs) Q Qoom := by
  have hp12_4 : (pc + 12#64) + 4#64 = pc + 16#64 := by bv_omega
  have hp16_4 : (pc + 16#64) + 4#64 = pc + 20#64 := by bv_omega
  have hp16_m16 : (pc + 16#64) + (-16#64) = pc := by bv_omega
  have hrun_it : ∀ l w, (s1.stxrIter l rs w).status = .Running := fun l w => by
    cases s1; cases rs <;> exact hrun1
  have hpc_it : ∀ l w, (s1.stxrIter l rs w).pc = pc + 12#64 := fun l w => by
    cases s1; cases rs <;> exact hpc1
  have hsp_it : ∀ l w, checkRegSPAligned (s1.stxrIter l rs w) rn = true := by
    intro l w; cases rn with
    | gpr _ | xzr => rfl
    | sp => cases rs with
      | gpr _ => exact hsp1
      | sp | xzr => simp [Reg.isNonZeroGpr] at hrs
  have hr64_it : ∀ l w r, (r != rs) = true → (s1.stxrIter l rs w).readReg64 r = s1.readReg64 r :=
    fun l w r hr => State.readReg64_writeReg64_ne (s1.withExclFails l) rs r w (reg_ne_of_bne hr)
  have h_ok : ∀ (l : List Bool) (w : BitVec 64), l.headD false = false →
      reaches_pc prog target_pc
        (((s1.withExclFails l.tail).writeReg .W32 rs 0#64).setPC (pc + 20#64)
          |>.setMem (s1.mem.writeSized sz ea (s1.readReg64 rt))) Q Qoom →
      reaches_pc prog target_pc (s1.stxrIter l rs w) Q Qoom := by
    intro l w hl hgoal
    apply reaches_pc_step (hrun_it l w) ((hpc_it l w).symm ▸ hf3)
    have hst : prog.evalInst (.stxr sz rel rs rn rt) (s1.stxrIter l rs w) =
        (((s1.withExclFails l.tail).writeReg .W32 rs 0#64).setPC (pc + 16#64)
          |>.setMem (s1.mem.writeSized sz ea (s1.readReg64 rt))) := by
      have hfail : (s1.stxrIter l rs w).exclWillFail = false := by cases s1; cases rs <;> exact hl
      have hsp' := hsp_it l w
      have haddr' : (s1.stxrIter l rs w).readReg64 rn = ea := (hr64_it l w rn hrn_s).trans haddr1
      have hrt' := hr64_it l w rt hrt_s
      have hmem' : (s1.stxrIter l rs w).mem = s1.mem := by cases s1; cases rs <;> rfl
      have hstep_o : (s1.stxrIter l rs w).stepExclOracle = s1.stxrIter l.tail rs w := by
        cases s1; cases rs <;> rfl
      dsimp only [Program.evalInst, execInstWithSvc]
      rw [hsp', haddr', halign, hmem', hcw, hfail, hrt', hstep_o]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      dsimp only [State.stxrIter, State.writeReg]
      rw [State.writeReg64_setMem, State.writeReg64_writeReg64_same]
      cases s1; cases rs <;> simp [State.withExclFails, State.writeReg64, State.advancePC,
        State.setPC, State.setMem, hpc1, hp12_4]
    rw [hst]
    let s_cb := (((s1.withExclFails l.tail).writeReg .W32 rs 0#64).setPC (pc + 16#64)
      |>.setMem (s1.mem.writeSized sz ea (s1.readReg64 rt)))
    have hrun_cb : s_cb.status = .Running := by cases s1; cases rs <;> exact hrun1
    have hf4_cb : prog.fetch s_cb.pc = some (.cbz .W32 true rs (-16#64)) := by
      have : s_cb.pc = pc + 16#64 := by cases s1; cases rs <;> rfl
      rw [this]; exact hf4
    apply reaches_pc_step hrun_cb hf4_cb
    have hcb : prog.evalInst (.cbz .W32 true rs (-16#64)) s_cb =
        (((s1.withExclFails l.tail).writeReg .W32 rs 0#64).setPC (pc + 20#64)
          |>.setMem (s1.mem.writeSized sz ea (s1.readReg64 rt))) := by
      have hrs0 : s_cb.readReg .W32 rs = 0#64 := by
        cases rs with
        | gpr idx =>
          have h31 : (idx == 31#5) = false := by simpa [Reg.isNonZeroGpr] using hrs
          cases s1; simp [s_cb, State.readReg, State.readReg32, State.readReg64, State.writeReg,
            State.writeReg64, State.setPC, State.setMem, State.withExclFails, RegFile.read, RegFile.write, h31]
        | sp | xzr => simp [Reg.isNonZeroGpr] at hrs
      dsimp only [Program.evalInst, execInstWithSvc]
      rw [hrs0]
      have hc0 : (((0#64 : BitVec 64) == 0#64) != true) = false := rfl
      rw [hc0]; simp only [Bool.false_eq_true, ↓reduceIte]
      cases s1; cases rs <;> simp [s_cb, State.advancePC, State.setPC, State.setMem,
        State.writeReg, State.writeReg64, State.withExclFails, hp16_4]
    rw [hcb]
    exact hgoal
  induction ef generalizing w_rs with
  | nil => exact h_ok [] w_rs rfl hsucc
  | cons b bs ih =>
    cases b with
    | false => exact h_ok (false :: bs) w_rs rfl (by simpa [List.dropWhile] using hsucc)
    | true =>
      apply reaches_pc_step (hrun_it (true :: bs) w_rs) ((hpc_it (true :: bs) w_rs).symm ▸ hf3)
      have hst : prog.evalInst (.stxr sz rel rs rn rt) (s1.stxrIter (true :: bs) rs w_rs) =
          (s1.stxrIter bs rs 1#64).setPC (pc + 16#64) := by
        have hfail : (s1.stxrIter (true :: bs) rs w_rs).exclWillFail = true := by
          cases s1; cases rs <;> rfl
        have hsp' := hsp_it (true :: bs) w_rs
        have haddr' : (s1.stxrIter (true :: bs) rs w_rs).readReg64 rn = ea :=
          (hr64_it (true :: bs) w_rs rn hrn_s).trans haddr1
        have hmem' : (s1.stxrIter (true :: bs) rs w_rs).mem = s1.mem := by cases s1; cases rs <;> rfl
        have hstep_o : (s1.stxrIter (true :: bs) rs w_rs).stepExclOracle = s1.stxrIter bs rs w_rs := by
          cases s1; cases rs <;> rfl
        dsimp only [Program.evalInst, execInstWithSvc]
        rw [hsp', haddr', halign, hmem', hcw, hfail, hstep_o]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        dsimp only [State.stxrIter, State.writeReg]
        rw [State.writeReg64_writeReg64_same]
        cases s1; cases rs <;> simp [State.withExclFails, State.writeReg64, State.advancePC,
          State.setPC, hpc1, hp12_4]
      rw [hst]
      have hrun_cb : ((s1.stxrIter bs rs 1#64).setPC (pc + 16#64)).status = .Running := by
        cases s1; cases rs <;> exact hrun1
      have hf4_cb : prog.fetch ((s1.stxrIter bs rs 1#64).setPC (pc + 16#64)).pc =
          some (.cbz .W32 true rs (-16#64)) := by
        have : ((s1.stxrIter bs rs 1#64).setPC (pc + 16#64)).pc = pc + 16#64 := rfl
        rw [this]; exact hf4
      apply reaches_pc_step hrun_cb hf4_cb
      have hcb : prog.evalInst (.cbz .W32 true rs (-16#64)) ((s1.stxrIter bs rs 1#64).setPC (pc + 16#64)) =
          (s1.setPC pc).stxrIter bs rs 1#64 := by
        have hrs1 : ((s1.stxrIter bs rs 1#64).setPC (pc + 16#64)).readReg .W32 rs = 1#64 := by
          cases rs with
          | gpr idx =>
            have h31 : (idx == 31#5) = false := by simpa [Reg.isNonZeroGpr] using hrs
            cases s1; simp [State.stxrIter, State.readReg, State.readReg32, State.readReg64,
              State.writeReg64, State.setPC, State.withExclFails, RegFile.read, RegFile.write, h31]
          | sp | xzr => simp [Reg.isNonZeroGpr] at hrs
        have hc1 : (((1#64 : BitVec 64) == 0#64) != true) = true := rfl
        dsimp only [Program.evalInst, execInstWithSvc]
        rw [hrs1, hc1]
        simp only [↓reduceIte]
        have hpc_cb : ((s1.stxrIter bs rs 1#64).setPC (pc + 16#64)).pc = pc + 16#64 := rfl
        rw [hpc_cb, hp16_m16]
        cases s1; cases rs <;> rfl
      rw [hcb]
      let s0 := (s1.setPC pc).stxrIter bs rs 1#64
      have hpc0 : s0.pc = pc := by cases s1; cases rs <;> rfl
      have hrun0 : s0.status = .Running := by cases s1; cases rs <;> exact hrun1
      have hsp0 : checkRegSPAligned s0 rn = true := by
        cases rn with
        | gpr _ | xzr => rfl
        | sp => cases rs with
          | gpr _ => exact hsp1
          | sp | xzr => simp [Reg.isNonZeroGpr] at hrs
      have hr_base : ∀ r, ((s1.setPC pc).withExclFails bs).readReg64 r = s1.readReg64 r := by
        intro r; cases s1; cases r <;> rfl
      have haddr0 : s0.readReg64 rn = ea :=
        ((State.readReg64_writeReg64_ne _ rs rn 1#64 (reg_ne_of_bne hrn_s)).trans (hr_base rn)).trans haddr1
      have hexp0 : s0.readReg w_op r_exp = exp64 := by
        have hr := (State.readReg64_writeReg64_ne _ rs r_exp 1#64 (reg_ne_of_bne hexp_s)).trans (hr_base r_exp)
        cases w_op <;> simpa [s0, State.stxrIter, State.readReg, State.readReg32, hr] using hexp1
      have hwr0 : s0.writeReg w_op rt_ld v_ld = s0 := by
        have hne' : rs ≠ rt_ld := (reg_ne_of_bne hld_s).symm
        cases w_op <;> {
          have hcomm : ∀ (st : State) v, ((st.setPC pc).withExclFails bs).writeReg64 rt_ld v =
              ((st.writeReg64 rt_ld v).setPC pc).withExclFails bs := by
            intro st v; cases st; cases rt_ld <;> rfl
          dsimp [s0, State.stxrIter, State.writeReg]
          rw [State.writeReg64_comm_or_same]; simp only [hne', ↓reduceIte, hcomm]
          exact congrArg (fun st => ((st.setPC pc).withExclFails bs).writeReg64 rs 1#64) hld_idem }
      have hps0 : (evalAddSub w_op .SUBS ((s0.writeReg w_op rt_ld v_ld).readReg w_op rt_ld)
          (shiftVal w_op exp64 .LSL 0) none).2 = some ps := by
        rw [hwr0]
        have hr := (State.readReg64_writeReg64_ne _ rs rt_ld 1#64 (reg_ne_of_bne hld_s)).trans (hr_base rt_ld)
        have hld0 : s0.readReg w_op rt_ld = s1.readReg w_op rt_ld := by
          cases w_op <;> simp [s0, State.stxrIter, State.readReg, State.readReg32, hr]
        rw [hld0]; exact hps
      have hcr0 : s0.mem.canRead ea sz.bytes = true := by cases s1; cases rs <;> exact hcr
      have hrd0 : s0.mem.readSized sz false ea = v_ld := by cases s1; cases rs <;> exact hrd
      refine step_ldxr_cmp_bne hw hpc0 hrun0 hf0 hf1 hf2 hexp_ld hsp0 haddr0 halign hcr0 hrd0 hexp0 hps0 ?_
      rw [hwr0, hcond]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hrestore : (s0.setPState ps).setPC (pc + 12#64) = s1.stxrIter bs rs 1#64 := by
        subst hps1; rw [← hpc1]
        cases s1; cases rs <;> rfl
      rw [hrestore]
      exact ih 1#64 (by simpa [List.dropWhile] using hsucc)

private theorem reaches_pc_cas_llsc_gen {prog : Program} {target_pc : BitVec 64}
    {s : State} {Q Qoom : State → Prop} {pc ea v_ld exp64 : BitVec 64}
    {sz : MemWidth} {w_op : Width} {acq rel : Bool} {rs rn rt rt_ld r_exp : Reg} {ps : PState}
    (hw : (match sz with | .X64 => .W64 | _ => .W32 : Width) = w_op)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hf0 : prog.fetch pc = some (.ldxr sz acq rn rt_ld))
    (hf1 : prog.fetch (pc + 4#64) = some (.addSubShift w_op .SUBS .xzr rt_ld r_exp .LSL 0))
    (hf2 : prog.fetch (pc + 8#64) = some (.bCond .NE 12#64))
    (hf3 : prog.fetch (pc + 12#64) = some (.stxr sz rel rs rn rt))
    (hf4 : prog.fetch (pc + 16#64) = some (.cbz .W32 true rs (-16#64)))
    (hregs : (rs.isNonZeroGpr && rt_ld.isNonZeroGpr && (rt_ld != rs) && (rn != rs) &&
      (rt != rs) && (r_exp != rs) && (rn != rt_ld) && (rt != rt_ld) && (r_exp != rt_ld)) = true)
    (hsp : checkRegSPAligned s rn = true) (haddr : s.readReg64 rn = ea)
    (halign : sz.isAligned ea = true)
    (hcr : s.mem.canRead ea sz.bytes = true) (hcw : s.mem.canWrite ea sz.bytes = true)
    (hrd : s.mem.readSized sz false ea = v_ld) (hexp : s.readReg w_op r_exp = exp64)
    (hps : (evalAddSub w_op .SUBS ((s.writeReg w_op rt_ld v_ld).readReg w_op rt_ld)
      (shiftVal w_op exp64 .LSL 0) none).2 = some ps)
    (hk_ne : ConditionHolds .NE ps = true →
      reaches_pc prog target_pc (((s.writeReg w_op rt_ld v_ld).setPState ps).setPC (pc + 20#64)) Q Qoom)
    (hk_eq : ConditionHolds .NE ps = false →
      reaches_pc prog target_pc
        (((((s.writeReg w_op rt_ld v_ld).setPState ps).stepExclLoop).writeReg .W32 rs 0#64).setPC (pc + 20#64)
          |>.setMem (s.mem.writeSized sz ea (s.readReg64 rt))) Q Qoom) :
    reaches_pc prog target_pc s Q Qoom := by
  simp only [Bool.and_eq_true] at hregs
  rcases hregs with ⟨⟨⟨⟨⟨⟨⟨⟨hrs, hld_gpr⟩, hld_s⟩, hrn_s⟩, hrt_s⟩, hexp_s⟩, hrn_ld⟩, hrt_ld⟩, hexp_ld⟩
  refine step_ldxr_cmp_bne hw hpc hrun hf0 hf1 hf2 hexp_ld hsp haddr halign hcr hrd hexp hps ?_
  by_cases hc : ConditionHolds .NE ps = true
  · rw [hc]; simp only [↓reduceIte]; exact hk_ne hc
  · have hcf : ConditionHolds .NE ps = false := Bool.eq_false_iff.mpr hc
    rw [hcf]; simp only [Bool.false_eq_true, ↓reduceIte]
    let s1 := ((s.writeReg w_op rt_ld v_ld).setPState ps).setPC (pc + 12#64)
    have hs1_self : s1 = s1.stxrIter s.exclFails rs (s1.readReg64 rs) := by
      have hexcl : s1.exclFails = s.exclFails := by cases s; cases w_op <;> cases rt_ld <;> rfl
      rw [← hexcl]
      cases s1 with | mk regs vregs sp pc' pstate mem tpidr fpsr bs' b fs o oi ef tr st sym sig =>
        cases rs with
        | gpr idx =>
          dsimp [State.stxrIter, State.withExclFails, State.writeReg64, State.readReg64]
          by_cases h31 : idx == 31#5 <;> simp [h31, RegFile.write, RegFile.read]
          cases regs; congr 1; funext k; by_cases hk : k = idx <;> simp [hk]
        | sp | xzr => rfl
    change reaches_pc prog target_pc s1 Q Qoom
    rw [hs1_self]
    have hpc1 : s1.pc = pc + 12#64 := by cases s; cases w_op <;> cases rt_ld <;> rfl
    have hrun1 : s1.status = .Running := by cases s; cases w_op <;> cases rt_ld <;> exact hrun
    have hps1 : s1.pstate = ps := by cases s; cases w_op <;> cases rt_ld <;> rfl
    have hsp1 : checkRegSPAligned s1 rn = true := by
      cases rn with
      | gpr _ | xzr => rfl
      | sp => cases rt_ld with
        | gpr _ => cases w_op <;> exact hsp
        | sp | xzr => simp [Reg.isNonZeroGpr] at hld_gpr
    have haddr1 : s1.readReg64 rn = ea := by
      simpa [s1, readReg64_writeReg_ne s w_op rt_ld rn v_ld hrn_ld] using haddr
    have hexp1 : s1.readReg w_op r_exp = exp64 := by
      cases w_op <;> {
        dsimp only [s1, State.readReg, State.readReg32]
        rw [State.readReg64_setPC, State.readReg64_setPState,
          readReg64_writeReg_ne s _ rt_ld r_exp v_ld hexp_ld]
        exact hexp }
    have hrt1 : s1.readReg64 rt = s.readReg64 rt := by
      simpa [s1] using readReg64_writeReg_ne s w_op rt_ld rt v_ld hrt_ld
    have hld_idem : s1.writeReg w_op rt_ld v_ld = s1 := by
      cases s; cases w_op <;> cases rt_ld with
      | gpr idx =>
        dsimp [s1, State.writeReg, State.writeReg64, State.setPState, State.setPC, RegFile.write]
        by_cases h31 : idx == 31#5 <;> simp [h31]
        congr 1; funext k; by_cases hk : k = idx <;> simp [hk]
      | sp | xzr => rfl
    have hps_s1 : (evalAddSub w_op .SUBS (s1.readReg w_op rt_ld) (shiftVal w_op exp64 .LSL 0) none).2 = some ps := by
      have : s1.readReg w_op rt_ld = (s.writeReg w_op rt_ld v_ld).readReg w_op rt_ld := by
        cases s; cases w_op <;> cases rt_ld <;> rfl
      rw [this]; exact hps
    have hm1 : s1.mem = s.mem := by cases s; cases w_op <;> cases rt_ld <;> rfl
    refine reaches_pc_cas_llsc_loop hw hpc1 hrun1 hps1 hf0 hf1 hf2 hf3 hf4
      hrs hrn_s hrt_s hld_s hexp_s hexp_ld hsp1 haddr1 halign
      (hm1 ▸ hcr) (hm1 ▸ hcw) (hm1 ▸ hrd) hexp1 hld_idem hps_s1 hcf s.exclFails _ ?_
    rw [hm1, hrt1]
    have hfin : (((s1.withExclFails (s.exclFails.dropWhile (· == true)).tail).writeReg .W32 rs 0#64).setPC (pc + 20#64)) =
        (((((s.writeReg w_op rt_ld v_ld).setPState ps).stepExclLoop).writeReg .W32 rs 0#64).setPC (pc + 20#64)) := by
      cases s; cases w_op <;> cases rt_ld <;> cases rs <;> rfl
    rw [hfin]; exact hk_eq hcf

/-- 32-bit 5-instruction outline-atomics LL/SC CAS loop (`ld(a)xr Wt_ld, [Xn]; cmp Wt_ld, W_exp;
    b.ne +12; st(l)xr Ws, Wt, [Xn]; cbnz Ws, -16`) over `((ea ↦₃₂ v0) ∗ F)`. -/
theorem SepWP.step_cas_llsc_retry32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc ea : BitVec 64} {acq rel : Bool} {rs rn rt rt_ld r_exp : Reg} {v0 exp new : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hf0 : prog.fetch pc = some (.ldxr .W32 acq rn rt_ld))
    (hf1 : prog.fetch (pc + 4#64) = some (.addSubShift .W32 .SUBS .xzr rt_ld r_exp .LSL 0))
    (hf2 : prog.fetch (pc + 8#64) = some (.bCond .NE 12#64))
    (hf3 : prog.fetch (pc + 12#64) = some (.stxr .W32 rel rs rn rt))
    (hf4 : prog.fetch (pc + 16#64) = some (.cbz .W32 true rs (-16#64)))
    (hregs : (rs.isNonZeroGpr && rt_ld.isNonZeroGpr && (rt_ld != rs) && (rn != rs) &&
      (rt != rs) && (r_exp != rs) && (rn != rt_ld) && (rt != rt_ld) && (r_exp != rt_ld)) = true)
    (hsp : checkRegSPAligned s rn = true) (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .W32 ea = true)
    (hexp : s.readReg32 r_exp = exp) (hnew : s.readReg32 rt = new)
    (hexec :
      let s_cmp := (s.writeReg32 rt_ld v0).setPState (subsPState32 v0 exp)
      (if v0 == exp then (s_cmp.stepExclLoop.writeReg32 rs 0#32).setPC (pc + 20#64)
       else s_cmp.setPC (pc + 20#64)) = s')
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (s'.setMem m') ((ea ↦₃₂ (if v0 == exp then new else v0)) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post oom := by
  intro R hm
  have hm' : s.mem ⊨ (ea ↦₃₂ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcr : s.mem.canRead ea 4 = true := (IsBlock.pointsTo32 ea v0).canRead (by decide) hm'
  have hcw : s.mem.canWrite ea 4 = true := (IsBlock.pointsTo32 ea v0).canWrite (by decide) hm'
  have hrd : s.mem.readSized .W32 false ea = v0.zeroExtend 64 := by
    simp [Memory.readSized, (IsBlock.pointsTo32 ea v0).read hm']
  have hexp64 : s.readReg .W32 r_exp = exp.zeroExtend 64 := by simp [State.readReg, hexp]
  have hld_gpr : rt_ld.isNonZeroGpr = true := by simp only [Bool.and_eq_true] at hregs; exact hregs.1.1.1.1.1.1.1.2
  have hrd_ld : (s.writeReg .W32 rt_ld (v0.zeroExtend 64)).readReg .W32 rt_ld = v0.zeroExtend 64 := by
    cases rt_ld with
    | gpr idx =>
      have h31 : (idx == 31#5) = false := by simpa [Reg.isNonZeroGpr] using hld_gpr
      cases s; simp [State.writeReg, State.readReg, State.readReg32, State.readReg64,
        State.writeReg64, RegFile.read, RegFile.write, h31]
    | sp | xzr => simp [Reg.isNonZeroGpr] at hld_gpr
  have hps : (evalAddSub .W32 .SUBS ((s.writeReg .W32 rt_ld (v0.zeroExtend 64)).readReg .W32 rt_ld)
      (shiftVal .W32 (exp.zeroExtend 64) .LSL 0) none).2 = some (subsPState32 v0 exp) := by
    rw [hrd_ld]; simp [shiftVal, shift32]
  refine reaches_pc_cas_llsc_gen rfl hpc hrun hf0 hf1 hf2 hf3 hf4 hregs hsp haddr halign
    hcr hcw hrd hexp64 hps (fun hc => ?_) (fun hc => ?_)
  · have hcmp_f : (v0 == exp) = false := by simpa [bne] using hc
    have hst : ((s.writeReg .W32 rt_ld (v0.zeroExtend 64)).setPState (subsPState32 v0 exp)).setPC (pc + 20#64) =
        s'.setMem s.mem := by
      rw [← hexec]; simp only [hcmp_f, Bool.false_eq_true, ↓reduceIte]
      cases s; cases rt_ld <;> simp [State.writeReg, State.writeReg32, State.setPState, State.setPC, State.setMem]
    rw [hst]; apply hnext s.mem R; simpa [hcmp_f] using hm
  · have hcmp_t : (v0 == exp) = true := by simpa [bne] using hc
    have hwr : s.mem.writeSized .W32 ea (s.readReg64 rt) = s.mem.write32 ea new := by
      simp [Memory.writeSized, ← hnew, State.readReg32]
    rw [hwr]
    have hst : (((((s.writeReg .W32 rt_ld (v0.zeroExtend 64)).setPState (subsPState32 v0 exp)).stepExclLoop).writeReg
        .W32 rs 0#64).setPC (pc + 20#64) |>.setMem (s.mem.write32 ea new)) =
        s'.setMem (s.mem.write32 ea new) := by
      rw [← hexec]; simp only [hcmp_t, ↓reduceIte]
      cases s; cases rt_ld <;> cases rs <;>
        simp [State.writeReg, State.writeReg32, State.setPState, State.stepExclLoop, State.setPC, State.setMem]
    rw [hst]; apply hnext (s.mem.write32 ea new) R
    simp only [hcmp_t, ↓reduceIte]; rw [sepConj_assoc]
    exact (IsBlock.pointsTo32 ea v0).write32 hm' new

/-- 64-bit 5-instruction outline-atomics LL/SC CAS loop (`ld(a)xr Xt_ld, [Xn]; cmp Xt_ld, X_exp;
    b.ne +12; st(l)xr Ws, Xt, [Xn]; cbnz Ws, -16`) over `((ea ↦₆₄ v0) ∗ F)`. -/
theorem SepWP.step_cas_llsc_retry64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc ea v0 exp new : BitVec 64} {acq rel : Bool} {rs rn rt rt_ld r_exp : Reg}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hf0 : prog.fetch pc = some (.ldxr .X64 acq rn rt_ld))
    (hf1 : prog.fetch (pc + 4#64) = some (.addSubShift .W64 .SUBS .xzr rt_ld r_exp .LSL 0))
    (hf2 : prog.fetch (pc + 8#64) = some (.bCond .NE 12#64))
    (hf3 : prog.fetch (pc + 12#64) = some (.stxr .X64 rel rs rn rt))
    (hf4 : prog.fetch (pc + 16#64) = some (.cbz .W32 true rs (-16#64)))
    (hregs : (rs.isNonZeroGpr && rt_ld.isNonZeroGpr && (rt_ld != rs) && (rn != rs) &&
      (rt != rs) && (r_exp != rs) && (rn != rt_ld) && (rt != rt_ld) && (r_exp != rt_ld)) = true)
    (hsp : checkRegSPAligned s rn = true) (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .X64 ea = true)
    (hexp : s.readReg64 r_exp = exp) (hnew : s.readReg64 rt = new)
    (hexec :
      let s_cmp := (s.writeReg64 rt_ld v0).setPState (subsPState64 v0 exp)
      (if v0 == exp then (s_cmp.stepExclLoop.writeReg32 rs 0#32).setPC (pc + 20#64)
       else s_cmp.setPC (pc + 20#64)) = s')
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (s'.setMem m') ((ea ↦₆₄ (if v0 == exp then new else v0)) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₆₄ v0) ∗ F) post oom := by
  intro R hm
  have hm' : s.mem ⊨ (ea ↦₆₄ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcr : s.mem.canRead ea 8 = true := (IsBlock.pointsTo64 ea v0).canRead (by decide) hm'
  have hcw : s.mem.canWrite ea 8 = true := (IsBlock.pointsTo64 ea v0).canWrite (by decide) hm'
  have hrd : s.mem.readSized .X64 false ea = v0 := by
    simp [Memory.readSized, (IsBlock.pointsTo64 ea v0).read hm']
  have hexp64 : s.readReg .W64 r_exp = exp := hexp
  have hld_gpr : rt_ld.isNonZeroGpr = true := by simp only [Bool.and_eq_true] at hregs; exact hregs.1.1.1.1.1.1.1.2
  have hrd_ld : (s.writeReg .W64 rt_ld v0).readReg .W64 rt_ld = v0 := by
    cases rt_ld with
    | gpr idx =>
      have h31 : (idx == 31#5) = false := by simpa [Reg.isNonZeroGpr] using hld_gpr
      cases s; simp [State.writeReg, State.readReg, State.readReg64,
        State.writeReg64, RegFile.read, RegFile.write, h31]
    | sp | xzr => simp [Reg.isNonZeroGpr] at hld_gpr
  have hps : (evalAddSub .W64 .SUBS ((s.writeReg .W64 rt_ld v0).readReg .W64 rt_ld)
      (shiftVal .W64 exp .LSL 0) none).2 = some (subsPState64 v0 exp) := by
    rw [hrd_ld]; simp [shiftVal, shift64]
  refine reaches_pc_cas_llsc_gen rfl hpc hrun hf0 hf1 hf2 hf3 hf4 hregs hsp haddr halign
    hcr hcw hrd hexp64 hps (fun hc => ?_) (fun hc => ?_)
  · have hcmp_f : (v0 == exp) = false := by simpa [bne] using hc
    have hst : ((s.writeReg .W64 rt_ld v0).setPState (subsPState64 v0 exp)).setPC (pc + 20#64) =
        s'.setMem s.mem := by
      rw [← hexec]; simp only [hcmp_f, Bool.false_eq_true, ↓reduceIte]
      cases s; cases rt_ld <;> rfl
    rw [hst]; apply hnext s.mem R; simpa [hcmp_f] using hm
  · have hcmp_t : (v0 == exp) = true := by simpa [bne] using hc
    have hwr : s.mem.writeSized .X64 ea (s.readReg64 rt) = s.mem.write64 ea new := by
      simp [Memory.writeSized, hnew]
    rw [hwr]
    have hst : (((((s.writeReg .W64 rt_ld v0).setPState (subsPState64 v0 exp)).stepExclLoop).writeReg
        .W32 rs 0#64).setPC (pc + 20#64) |>.setMem (s.mem.write64 ea new)) =
        s'.setMem (s.mem.write64 ea new) := by
      rw [← hexec]; simp only [hcmp_t, ↓reduceIte]
      cases s; cases rt_ld <;> cases rs <;> rfl
    rw [hst]; apply hnext (s.mem.write64 ea new) R
    simp only [hcmp_t, ↓reduceIte]; rw [sepConj_assoc]
    exact (IsBlock.pointsTo64 ea v0).write64 hm' new


end ProofLib
