/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Std.Tactic.BVDecide
public import Arm64
public import ProofLib.SimpAttrs
public import ProofLib.CoreLemmas
public import ProofLib.Lemmas
public import ProofLib.SepLogic.Frame
public import ProofLib.Abi.Aapcs
public import ProofLib.SepLogic
public import ProofLib.SepLogic.Bytes
public import ProofLib.ObjectLoad
public import ProofLib.Hoare.Safety
public import ProofLib.VCGen
public import ProofLib.LitNorm
public import ProofLib.BV.WidthNorm
public import ProofLib.SepLogic.WP.Defs
public import ProofLib.SepLogic.CondClassify
public import ProofLib.BV.Arith
public import ProofLib.SepLogic.WP.StateNorm
public import ProofLib.SepLogic.WP.Access

/-!
# Core `SepWP` Structural, Conditional Compare, and Load/Store Rules

Core `SepWP` structural lemmas, pure instruction steps, conditional compare (`CCMP` / `CCMN`)
rules, and 8-bit and 64-bit load/store step rules.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-! ## Structural and Pure-Step Rules -/

/-- Reflexive completion rule for `SepWP` when `s.pc = target_pc`. -/
theorem SepWP.done {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = target_pc)
    (hrun : s.status = .Running)
    (hpost : post s P) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  exact reaches_pc_refl hpc hrun ⟨P, hm, hpost⟩

/-- Elimination rule for `SepWP`: instantiate with frame `R` and initial memory `s.mem ⊨ P ∗ R`. -/
theorem SepWP.elim {prog : Program} {target_pc : BitVec 64}
    {s : State} {P R : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog target_pc s P post oom) (hm : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem) :
    ∃ sf, Steps prog s sf ∧
      ((sf.pc = target_pc ∧ sf.status = .Running ∧
        ∃ P_f, (sf.mem ⊨ P_f ∗ R) ∧ post sf P_f) ∨
       (sf.status = .OutOfMemory ∧ (sf.mem ⊨ oom sf ∗ R))) :=
  h R hm hL

/-- Extract a concrete `reaches_pc` execution witness from a `SepWP` proof (with `oom = ⌜False⌝`)
    for any frame `R` satisfying `s.mem ⊨ P ∗ R`. -/
theorem SepWP.reaches_of_sepWP {prog : Program} {target_pc : BitVec 64}
    {s : State} {P R : SepProp} {post : State → Prop}
    (h : SepWP prog target_pc s P (fun sf _ => post sf))
    (hm : s.mem ⊨ P ∗ R) :
    reaches_pc prog target_pc s post := fun hL => by
  obtain ⟨sf, hs, ⟨hpc, hrun, _, _, hp⟩ | ⟨_, hoom⟩⟩ := SepWP.elim h hm hL
  · exact ⟨sf, hs, Or.inl ⟨hpc, hrun, hp⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

abbrev reaches_of_sepWP := @SepWP.reaches_of_sepWP

/-- Consequence / monotonicity rule for `SepWP`. -/
theorem SepWP.mono {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post post' : State → SepProp → Prop} {oom oom' : State → SepProp}
    (h : SepWP prog target_pc s P post oom)
    (himp : ∀ sf P_f, sf.pc = target_pc → sf.status = .Running → post sf P_f → post' sf P_f)
    (hoom : ∀ sf R, sf.status = .OutOfMemory → (sf.mem ⊨ oom sf ∗ R) → (sf.mem ⊨ oom' sf ∗ R) := by
      intro _ _ _ ho; first | exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj ho) :
    SepWP prog target_pc s P post' oom' := by
  intro R hm
  refine reaches_pc_mono (h R hm) ?_ (fun sf hst ho => hoom sf R hst ho)
  intro sf hpc hrun ⟨P_f, hmf, hp⟩
  exact ⟨P_f, hmf, himp sf P_f hpc hrun hp⟩

/-- Spatial entailment weakening on the precondition of `SepWP`. -/
theorem SepWP.weaken_pre {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hent : P ⊢ P')
    (h : SepWP prog target_pc s P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  exact h R (Satisfies.mono (sepConj_mono_left hent) hm)

/-- State-local, frame-wise precondition weakening for `SepWP`: it suffices that `P ∗ R` implies
    `P' ∗ R` in the current memory `s.mem`, for every frame `R` (weaker than `P ⊢ P'`). -/
theorem SepWP.weaken_pre_frame {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hent : ∀ R : SepProp, s.mem ⊨ P ∗ R → s.mem ⊨ P' ∗ R)
    (h : SepWP prog target_pc s P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  exact h R (hent R hm)

/-- Pure (non-memory) instruction step rule for `SepWP`. -/
theorem SepWP.step_pure {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {inst : Instr}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst (s.setPC pc) = s')
    (hmem : s'.mem = s.mem)
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hs_pc : s.setPC pc = s := by
    cases s
    simp [State.setPC] at hpc ⊢
    exact hpc.symm
  have hfetch' : prog.fetch s.pc = some inst := hpc.symm ▸ hfetch
  have hexec' : prog.evalInst inst s = s' := by rw [← hs_pc, hexec]
  apply reaches_pc_step hrun hfetch'
  rw [hexec']
  apply hnext R
  rwa [hmem]

/-- Pure instruction step rule for `SepWP` specialized to `s = s0.setPC pc`, avoiding the
    redundant `hpc` subgoal and redundant `.setPC pc` wrapper on `s`. -/
theorem SepWP.step_pure_setPC {prog : Program} {target_pc : BitVec 64}
    {s0 s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {inst : Instr}
    (hrun : (s0.setPC pc).status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst (s0.setPC pc) = s')
    (hmem : s'.mem = s0.mem)
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc (s0.setPC pc) P post oom := by
  intro R hm
  apply reaches_pc_step hrun hfetch
  rw [hexec]
  apply hnext R
  rwa [hmem, ← State.mem_setPC s0 pc]

/-- Pure instruction step rule for `SepWP` specialized to `s = (s0.setPC pc).setMem m`
    (the state shape after a store instruction), avoiding `hpc` and `.setPC pc` wrapping. -/
theorem SepWP.step_pure_setMem_setPC {prog : Program} {target_pc : BitVec 64}
    {s0 s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {m : Memory} {inst : Instr}
    (hrun : ((s0.setPC pc).setMem m).status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst ((s0.setPC pc).setMem m) = s')
    (hmem : s'.mem = m)
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc ((s0.setPC pc).setMem m) P post oom := by
  intro R hm
  have hfetch' : prog.fetch ((s0.setPC pc).setMem m).pc = some inst := by
    rw [State.pc_setMem, State.pc_setPC]
    exact hfetch
  apply reaches_pc_step hrun hfetch'
  rw [hexec]
  apply hnext R
  rwa [hmem]

/-! ## Conditional Compare (`CCMP` / `CCMN`)

`execCondCompare` branches over the entire `State`, preventing `SepWP.step_pure` from discharging
`s'.mem = s.mem` under a symbolic condition. The rules below push the branch into the `PState`
update (`s.setPState (if ConditionHolds cond s.pstate then flags else ofBits4 nzcv)`), keeping
memory syntactically unchanged so downstream `CSET` or `B.cond` steps simplify via
`conditionHolds_ite`. -/

/-- `ConditionHolds` distributes over an `if` on the flag state (as produced by `CCMP`/`CCMN`). -/
@[simp, arm64_norm, wp_norm]
theorem conditionHolds_ite (cond : CondCode) (c : Prop) [Decidable c] (ps1 ps2 : PState) :
    ConditionHolds cond (if c then ps1 else ps2) =
      if c then ConditionHolds cond ps1 else ConditionHolds cond ps2 := by
  split <;> rfl

-- `evalAddSub_*_subs`/`_adds` produce `some flags`; `SepWP.step_ccmp_*` wrap them in `getD`.
attribute [arm64_norm, wp_norm] Option.getD_some

/-- Shared soundness core for the conditional compare rules: mirrors `execCondCompare` exactly,
    with the condition pushed into the `PState` update. -/
theorem SepWP.step_condCompare {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {inst : Instr} {w : Width} {isSub isImm : Bool}
    {rn rm : Reg} {rhs : BitVec 64} {nzcv : BitVec 4} {cond : CondCode}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hinst : prog.evalInst inst s = execCondCompare w isSub isImm rn rhs rm nzcv cond s)
    (hexec : (s.setPState
        (if ConditionHolds cond s.pstate then
          ((evalAddSub w (if isSub then .SUBS else .ADDS) (s.readReg w rn)
            (if isImm then rhs else s.readReg w rm) none).2.getD s.pstate)
        else PState.ofBits4 nzcv)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some inst := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst inst s = s' := by
    rw [hinst, ← hexec]
    simp only [execCondCompare]
    split
    · generalize evalAddSub w (if isSub then .SUBS else .ADDS) (s.readReg w rn)
        (if isImm then rhs else s.readReg w rm) none = res
      obtain ⟨r, _ | ps⟩ := res <;>
        simp [State.advancePC, State.setPC, State.setPState, hpc]
    · simp [State.advancePC, State.setPC, State.setPState, hpc]
  rw [hstep]
  apply hnext R
  rw [← hexec]; exact hm

/-- `CCMP Rn, Rm, #nzcv, cond` (32- and 64-bit) step rule for `SepWP`
    (`execCondCompare w true false`). -/
theorem SepWP.step_ccmp_reg {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {w : Width} {src1 src2 : Reg} {nzcv : BitVec 4} {cond : CondCode}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.condCompareReg w true src1 src2 nzcv cond))
    (hexec : (s.setPState
        (if ConditionHolds cond s.pstate then
          ((evalAddSub w .SUBS (s.readReg w src1) (s.readReg w src2) none).2.getD
            s.pstate)
        else PState.ofBits4 nzcv)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_condCompare (isSub := true) (isImm := false) (rhs := 0#64) hpc hrun hfetch
    rfl hexec hnext

/-- `CCMP Rn, #imm, #nzcv, cond` (32- and 64-bit) step rule for `SepWP`
    (`execCondCompare w true true`). -/
theorem SepWP.step_ccmp_imm {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {w : Width} {src1 : Reg} {imm : BitVec 5} {nzcv : BitVec 4} {cond : CondCode}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.condCompareImm w true src1 imm nzcv cond))
    (hexec : (s.setPState
        (if ConditionHolds cond s.pstate then
          ((evalAddSub w .SUBS (s.readReg w src1) (imm.zeroExtend 64) none).2.getD
            s.pstate)
        else PState.ofBits4 nzcv)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_condCompare (isSub := true) (isImm := true) (rm := .xzr) hpc hrun hfetch
    rfl hexec hnext

/-- `CCMN Rn, Rm, #nzcv, cond` (32- and 64-bit) step rule for `SepWP`
    (`execCondCompare w false false`). -/
theorem SepWP.step_ccmn_reg {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {w : Width} {src1 src2 : Reg} {nzcv : BitVec 4} {cond : CondCode}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.condCompareReg w false src1 src2 nzcv cond))
    (hexec : (s.setPState
        (if ConditionHolds cond s.pstate then
          ((evalAddSub w .ADDS (s.readReg w src1) (s.readReg w src2) none).2.getD
            s.pstate)
        else PState.ofBits4 nzcv)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_condCompare (isSub := false) (isImm := false) (rhs := 0#64) hpc hrun hfetch
    rfl hexec hnext

/-- `CCMN Rn, #imm, #nzcv, cond` (32- and 64-bit) step rule for `SepWP`
    (`execCondCompare w false true`). -/
theorem SepWP.step_ccmn_imm {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {w : Width} {src1 : Reg} {imm : BitVec 5} {nzcv : BitVec 4} {cond : CondCode}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.condCompareImm w false src1 imm nzcv cond))
    (hexec : (s.setPState
        (if ConditionHolds cond s.pstate then
          ((evalAddSub w .ADDS (s.readReg w src1) (imm.zeroExtend 64) none).2.getD
            s.pstate)
        else PState.ofBits4 nzcv)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_condCompare (isSub := false) (isImm := true) (rm := .xzr) hpc hrun hfetch
    rfl hexec hnext

/-- 8-bit load (`LDRB Wt, [addr]`) step rule for `SepWP`: looks up `(ea ↦₈ v)` in `P` via `SepLoad8`. -/
theorem SepWP.step_ldr8 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 8}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .B8 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad8 ea P v)
    (hexec : ((applyWriteback s wb).writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .B8 false rt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read8 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 1 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W32 .B8 false rt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- 8-bit unscaled load (`LDURB Wt, [addr]`) step rule for `SepWP`: looks up `(ea ↦₈ v)` in `P` via `SepLoad8`. -/
theorem SepWP.step_ldur8 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 8}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .B8 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad8 ea P v)
    (hexec : ((applyWriteback s wb).writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldr8 hpc hrun hfetch hsp haddr hload hexec hnext

/-- 8-bit signed load (`LDRSB Wt/Xt, [addr]`) step rule for `SepWP`: looks up `(ea ↦₈ v)` in `P` via `SepLoad8`. -/
theorem SepWP.step_ldrsb {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {w : RegWidth} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 8}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr w .B8 true rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad8 ea P v)
    (hexec : ((applyWriteback s wb).writeReg w rt (v.signExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr w .B8 true rt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read8 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 1 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr w .B8 true rt addr) s = s' := by
    rw [← hexec]
    cases w <;> cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases w <;> cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- 8-bit signed unscaled load (`LDURSB Wt/Xt, [addr]`) step rule for `SepWP`: looks up `(ea ↦₈ v)` in `P` via `SepLoad8`. -/
theorem SepWP.step_ldursb {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {w : RegWidth} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 8}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr w .B8 true rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad8 ea P v)
    (hexec : ((applyWriteback s wb).writeReg w rt (v.signExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldrsb hpc hrun hfetch hsp haddr hload hexec hnext

/-- 8-bit store (`STRB Wt, [addr]`) step rule for `SepWP`: updates `(ea ↦₈ _)` to `(ea ↦₈ val)`
    in `P` via `SepStore8` and abstracts the post-store memory to a fresh variable `m'`. -/
theorem SepWP.step_str8 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 8}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg32 rt).truncate 8 = val)
    (hstore : SepStore8 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .B8 rt addr) := hpc.symm ▸ hfetch
  have htrunc : (s.readReg64 rt).truncate 8 = val := by
    rw [← bitvec_truncate8_truncate32]
    exact hval
  let m' := s.mem.write8 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea _ = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .B8 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact hnext m' R hm'

/-- 8-bit unscaled store (`STURB Wt, [addr]`) step rule for `SepWP`: updates `(ea ↦₈ _)` to `(ea ↦₈ val)`
    in `P` via `SepStore8` and abstracts the post-store memory to a fresh variable `m'`. -/
theorem SepWP.step_stur8 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 8}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg32 rt).truncate 8 = val)
    (hstore : SepStore8 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_str8 hpc hrun hfetch hsp haddr hval hstore hexec hnext

/-- 64-bit load (`LDR Xd, [addr]`) step rule for `SepWP`: looks up `(ea ↦₆₄ v)` in `P` via `SepLoad64`. -/
theorem SepWP.step_ldr64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W64 .X64 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad64 ea P v)
    (hexec : ((applyWriteback s wb).writeReg64 rt v).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W64 .X64 false rt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read64 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 8 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W64 .X64 false rt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- 64-bit store (`STR Xt, [addr]`) step rule for `SepWP`: updates `(ea ↦₆₄ _)` to `(ea ↦₆₄ val)`
    in `P` via `SepStore64` and abstracts the post-store memory to a fresh variable `m'`. -/
theorem SepWP.step_str64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .X64 rt addr) := hpc.symm ▸ hfetch
  let m' := s.mem.write64 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea _ = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .X64 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact hnext m' R hm'

/-- 64-bit store pair (`STP Xt1, Xt2, [addr]`) step rule for `SepWP`: updates `ea` and `ea + 8`
    in `P` via `SepStore64` and abstracts the post-store memory to a fresh variable `m'`. -/
theorem SepWP.step_stp64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1)
    (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1)
    (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W64 rt1 rt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact hnext m2 R hm2

/-- 64-bit load pair (`LDP Xt1, Xt2, [addr]`) step rule for `SepWP`: looks up `ea` and `ea + 8`
    in `P` via `SepLoad64`. -/
theorem SepWP.step_ldp64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldp .W64 false rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hload1 : SepLoad64 ea P v1)
    (hload2 : SepLoad64 ea2 P v2)
    (hexec : (((applyWriteback s wb).writeReg64 rt1 v1).writeReg64 rt2 v2).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldp .W64 false rt1 rt2 addr) := hpc.symm ▸ hfetch
  have hread1 : s.mem.read64 ea = v1 := hload1.load hm
  have hread2 : s.mem.read64 ea2 = v2 := hload2.load hm
  have hcan1 : s.mem.canRead ea 8 = true := hload1.readable hm
  have hcan2 : s.mem.canRead ea2 8 = true := hload2.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldp .W64 false rt1 rt2 addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdp, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hea2, hread1, hread2, hcan1, hcan2,
      MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

theorem Memory.canRead_4_of_8 {m : Memory} {ea : BitVec 64} (h : m.canRead ea 8 = true) :
    m.canRead ea 4 = true := by
  have h8 : (m.allPerm (·.r) ea (4 + 4) && m.allNoLazyFree ea (4 + 4)) = true := h
  rw [Memory.allPerm_add, Memory.allNoLazyFree_add] at h8
  simp only [Bool.and_eq_true] at h8
  simp only [Memory.canRead, Bool.and_eq_true]
  exact ⟨h8.1.1, h8.2.1⟩

theorem Memory.canRead_hi4_of_8 {m : Memory} {base : BitVec 64} (h : m.canRead base 8 = true) :
    m.canRead (base + 4#64) 4 = true := by
  have h8 : (m.allPerm (·.r) base (4 + 4) && m.allNoLazyFree base (4 + 4)) = true := h
  rw [Memory.allPerm_add, Memory.allNoLazyFree_add] at h8
  simp only [Bool.and_eq_true] at h8
  simp only [Memory.canRead, Bool.and_eq_true]
  exact ⟨h8.1.2, h8.2.2⟩

theorem Memory.canWrite_4_of_8 {m : Memory} {ea : BitVec 64} (h : m.canWrite ea 8 = true) :
    m.canWrite ea 4 = true := by
  have h8 : m.allPerm (fun p => p.w && !p.x) ea (4 + 4) = true := h
  rw [Memory.allPerm_add, Bool.and_eq_true] at h8
  exact h8.1

theorem Memory.canWrite_hi4_of_8 {m : Memory} {base : BitVec 64} (h : m.canWrite base 8 = true) :
    m.canWrite (base + 4#64) 4 = true := by
  have h8 : m.allPerm (fun p => p.w && !p.x) base (4 + 4) = true := h
  rw [Memory.allPerm_add, Bool.and_eq_true] at h8
  exact h8.2

theorem Memory.canRead_16_of_8_8 {m : Memory} {ea : BitVec 64}
    (h1 : m.canRead ea 8 = true) (h2 : m.canRead (ea + 8#64) 8 = true) :
    m.canRead ea 16 = true := by
  simp only [Memory.canRead, Bool.and_eq_true] at h1 h2
  change (m.allPerm (·.r) ea (8 + 8) && m.allNoLazyFree ea (8 + 8)) = true
  rw [Memory.allPerm_add, Memory.allNoLazyFree_add]
  simp only [Bool.and_eq_true]
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

theorem Memory.canWrite_16_of_8_8 {m : Memory} {ea : BitVec 64}
    (h1 : m.canWrite ea 8 = true) (h2 : m.canWrite (ea + 8#64) 8 = true) :
    m.canWrite ea 16 = true := by
  change m.allPerm (fun p => p.w && !p.x) ea (8 + 8) = true
  rw [Memory.allPerm_add, Bool.and_eq_true]
  exact ⟨h1, h2⟩

theorem Memory.read32_eq_truncate_read64 (m : Memory) (ea : BitVec 64) :
    m.read32 ea = (m.read64 ea).truncate 32 := by
  unfold Memory.read32 Memory.read64
  bv_bits

theorem Memory.read32_add4_eq_extract_read64 (m : Memory) (base : BitVec 64) :
    m.read32 (base + 4#64) = (m.read64 base).extractLsb' 32 32 := by
  unfold Memory.read32 Memory.read64
  have h0 : base + 4#64 + 0#64 = base + 4#64 := by bv_decide
  have h1 : base + 4#64 + 1#64 = base + 5#64 := by bv_decide
  have h2 : base + 4#64 + 2#64 = base + 6#64 := by bv_decide
  have h3 : base + 4#64 + 3#64 = base + 7#64 := by bv_decide
  rw [h0, h1, h2, h3]
  bv_decide

theorem Memory.read8_write32_eq_read8_write64_lo (m : Memory) (ea a : BitVec 64)
    (val32 : BitVec 32) (old64 new64 : BitVec 64)
    (hold : m.read64 ea = old64)
    (hnew : (old64 &&& 0xffffffff00000000#64) ||| val32.zeroExtend 64 = new64) :
    (m.write32 ea val32).read8 a = (m.write64 ea new64).read8 a := by
  subst hold hnew
  rw [Memory.read8_write32, Memory.read8_write64]
  have hb0 : (((m.read64 ea &&& 0xffffffff00000000#64) ||| val32.zeroExtend 64).extractLsb' 0 8) =
      val32.extractLsb' 0 8 := by bv_bits
  have hb1 : (((m.read64 ea &&& 0xffffffff00000000#64) ||| val32.zeroExtend 64).extractLsb' 8 8) =
      val32.extractLsb' 8 8 := by bv_bits
  have hb2 : (((m.read64 ea &&& 0xffffffff00000000#64) ||| val32.zeroExtend 64).extractLsb' 16 8) =
      val32.extractLsb' 16 8 := by bv_bits
  have hb3 : (((m.read64 ea &&& 0xffffffff00000000#64) ||| val32.zeroExtend 64).extractLsb' 24 8) =
      val32.extractLsb' 24 8 := by bv_bits
  have hb4 : (((m.read64 ea &&& 0xffffffff00000000#64) ||| val32.zeroExtend 64).extractLsb' 32 8) =
      m.read8 (ea + 4#64) := by unfold Memory.read64; bv_bits
  have hb5 : (((m.read64 ea &&& 0xffffffff00000000#64) ||| val32.zeroExtend 64).extractLsb' 40 8) =
      m.read8 (ea + 5#64) := by unfold Memory.read64; bv_bits
  have hb6 : (((m.read64 ea &&& 0xffffffff00000000#64) ||| val32.zeroExtend 64).extractLsb' 48 8) =
      m.read8 (ea + 6#64) := by unfold Memory.read64; bv_bits
  have hb7 : (((m.read64 ea &&& 0xffffffff00000000#64) ||| val32.zeroExtend 64).extractLsb' 56 8) =
      m.read8 (ea + 7#64) := by unfold Memory.read64; bv_bits
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  by_cases h7 : a = ea + 7#64
  · subst h7; simp
  · by_cases h6 : a = ea + 6#64
    · subst h6; simp
    · by_cases h5 : a = ea + 5#64
      · subst h5; simp
      · by_cases h4 : a = ea + 4#64
        · subst h4; simp
        · simp [h7, h6, h5, h4]

theorem Memory.read8_write32_eq_read8_write64_hi (m : Memory) (base ea a : BitVec 64)
    (val32 : BitVec 32) (old64 new64 : BitVec 64)
    (hbase : ea - 4#64 = base)
    (hold : m.read64 base = old64)
    (hnew : (old64 &&& 0x00000000ffffffff#64) ||| ((val32.zeroExtend 64) <<< 32) = new64) :
    (m.write32 ea val32).read8 a = (m.write64 base new64).read8 a := by
  have hea : ea = base + 4#64 := by rw [← hbase]; bv_bits
  subst hea hold hnew
  rw [Memory.read8_write32, Memory.read8_write64]
  have ha3 : base + 4#64 + 3#64 = base + 7#64 := by bv_bits
  have ha2 : base + 4#64 + 2#64 = base + 6#64 := by bv_bits
  have ha1 : base + 4#64 + 1#64 = base + 5#64 := by bv_bits
  rw [ha3, ha2, ha1]
  have hb0 : (((m.read64 base &&& 0x00000000ffffffff#64) ||| ((val32.zeroExtend 64) <<< 32)).extractLsb' 0 8) =
      m.read8 base := by
    have h0 : base + 0#64 = base := by bv_bits
    unfold Memory.read64; rw [h0]; bv_bits
  have hb1 : (((m.read64 base &&& 0x00000000ffffffff#64) ||| ((val32.zeroExtend 64) <<< 32)).extractLsb' 8 8) =
      m.read8 (base + 1#64) := by unfold Memory.read64; bv_bits
  have hb2 : (((m.read64 base &&& 0x00000000ffffffff#64) ||| ((val32.zeroExtend 64) <<< 32)).extractLsb' 16 8) =
      m.read8 (base + 2#64) := by unfold Memory.read64; bv_bits
  have hb3 : (((m.read64 base &&& 0x00000000ffffffff#64) ||| ((val32.zeroExtend 64) <<< 32)).extractLsb' 24 8) =
      m.read8 (base + 3#64) := by unfold Memory.read64; bv_bits
  have hb4 : (((m.read64 base &&& 0x00000000ffffffff#64) ||| ((val32.zeroExtend 64) <<< 32)).extractLsb' 32 8) =
      val32.extractLsb' 0 8 := by bv_bits
  have hb5 : (((m.read64 base &&& 0x00000000ffffffff#64) ||| ((val32.zeroExtend 64) <<< 32)).extractLsb' 40 8) =
      val32.extractLsb' 8 8 := by bv_bits
  have hb6 : (((m.read64 base &&& 0x00000000ffffffff#64) ||| ((val32.zeroExtend 64) <<< 32)).extractLsb' 48 8) =
      val32.extractLsb' 16 8 := by bv_bits
  have hb7 : (((m.read64 base &&& 0x00000000ffffffff#64) ||| ((val32.zeroExtend 64) <<< 32)).extractLsb' 56 8) =
      val32.extractLsb' 24 8 := by bv_bits
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  by_cases h7 : a = base + 7#64
  · subst h7; simp
  · by_cases h6 : a = base + 6#64
    · subst h6; simp
    · by_cases h5 : a = base + 5#64
      · subst h5; simp
      · by_cases h4 : a = base + 4#64
        · subst h4; simp
        · by_cases h3 : a = base + 3#64
          · subst h3; simp
          · by_cases h2 : a = base + 2#64
            · subst h2; simp
            · by_cases h1 : a = base + 1#64
              · subst h1; simp
              · by_cases h0 : a = base
                · subst h0; simp
                · simp [h7, h6, h5, h4, h3, h2, h1, h0]


end ProofLib
