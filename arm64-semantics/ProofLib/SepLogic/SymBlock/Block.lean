/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.SymBlock.Step
public import ProofLib.SepLogic.WP.Defs
import Arm64.Trusted.Spec.SepLogic

/-!
# Reflective Whole-Block Symbolic Execution Checker and Block Rule

Defines instruction tables (`SymBlock.Tbl`, `TblOK`), the hint-driven reflective fetch-execute loop
(`SymBlock.step`, `SymBlock.run`), its soundness theorem (`run_sound`), and the whole-block
separation-logic rules `SepWP_block` and `SepWPp_block`.
-/

@[expose] public section

namespace ProofLib.SymBlock

open Arm64

/-! ## Instruction tables -/

/-- Block instructions keyed by offset from the block base `b`. -/
abbrev Tbl := List (BitVec 64 × SymInsn)

/-- Every table entry is what `prog` fetches at `b + offset`. -/
def TblOK (prog : Program) (b : BitVec 64) (env : Env) : Tbl → Prop
  | [] => True
  | (o, si) :: t => prog.fetch (b + o) = some (si.toInstr env (b + o)) ∧ TblOK prog b env t

/-- First table entry at offset `o`. -/
def tblLookup : Tbl → BitVec 64 → Option SymInsn
  | [], _ => none
  | (o, si) :: t, x => if o = x then some si else tblLookup t x

theorem tblLookup_sound {prog : Program} {b : BitVec 64} {env : Env} :
    ∀ {tbl : Tbl} {o : BitVec 64} {si : SymInsn},
      TblOK prog b env tbl → tblLookup tbl o = some si →
      prog.fetch (b + o) = some (si.toInstr env (b + o))
  | [], _, _, _, h => by simp [tblLookup] at h
  | (o', si') :: t, o, si, ⟨h1, h2⟩, h => by
    unfold tblLookup at h
    split at h
    · subst_vars; cases h; exact h1
    · exact tblLookup_sound h2 h

/-- Instruction at offset `o`: the head of the cursor `cur` if it matches (O(1) for straight-line
    code, whose table is in execution order), otherwise a search of the whole table. Returns the
    advanced cursor. -/
def fetchCur (tbl cur : Tbl) (o : BitVec 64) : Option SymInsn × Tbl :=
  match cur with
  | (o', si) :: t => if o' = o then (some si, t) else (tblLookup tbl o, cur)
  | [] => (tblLookup tbl o, [])

theorem fetchCur_sound {prog : Program} {b : BitVec 64} {env : Env} {tbl cur cur' : Tbl}
    {o : BitVec 64} {si : SymInsn} (htbl : TblOK prog b env tbl) (hcur : TblOK prog b env cur)
    (h : fetchCur tbl cur o = (some si, cur')) :
    prog.fetch (b + o) = some (si.toInstr env (b + o)) ∧ TblOK prog b env cur' := by
  unfold fetchCur at h
  split at h
  · rename_i o' si' t
    split at h
    · simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst_vars
      exact hcur
    · simp only [Prod.mk.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      exact ⟨tblLookup_sound htbl h1, hcur⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    exact ⟨tblLookup_sound htbl h1, trivial⟩

/-! ## The block checker -/

/-- One fetch-execute step at a function-relative `pc`; also returns the advanced cursor. -/
def step (base : SExpr) (tbl cur : Tbl) (ss : SState) (h : Hint) : Option ((SState × List SProp) × Tbl) :=
  match ss.pc with
  | .rel o =>
    match fetchCur tbl cur o with
    | (some si, cur') => (stepSymInsn base ss si h).map (·, cur')
    | (none, _) => none
  | .abs _ => none

/-- Run one step per hint with cursor `cur`, concatenating the residual obligations. -/
def runC (base : SExpr) (tbl : Tbl) : Tbl → List Hint → SState → Option (SState × List SProp)
  | _, [], ss => some (ss, [])
  | cur, h :: hs, ss =>
    match step base tbl cur ss h with
    | some ((ss1, o1), cur') =>
      match runC base tbl cur' hs ss1 with
      | some (ss2, o2) => some (ss2, o1 ++ o2)
      | none => none
    | none => none

/-- Run one step per hint (cursor starts at the head of the table). -/
def run (base : SExpr) (tbl : Tbl) (hints : List Hint) (ss : SState) :
    Option (SState × List SProp) :=
  runC base tbl tbl hints ss

/-! ## Soundness -/

section Soundness

variable {prog : Program} {b : BitVec 64} {env : Env} {tbl : Tbl}

theorem step_sound {base : SExpr} (hbase : base.eval env = b) (htbl : TblOK prog b env tbl)
    {cur cur' : Tbl} (hcur : TblOK prog b env cur) {ss ss' : SState} {h : Hint} {obl : List SProp}
    {s0 : State} {m : Memory} {R : SepProp} {tgt : BitVec 64} {post oom : State → Prop}
    (hlen : ss.regs.length = 31) (hvval : VRegsValid ss.vregs)
    (hstep : step base tbl cur ss h = some ((ss', obl), cur'))
    (hobl : allHold env obl) (hm : m ⊨ cellsProp env ss.cells ∗ R)
    (hnext : ∀ m', (m' ⊨ cellsProp env ss'.cells ∗ R) → ss'.regs.length = 31 →
      VRegsValid ss'.vregs → TblOK prog b env cur' →
      reaches_pc prog tgt (ss'.toState b env s0 m') post oom) :
    reaches_pc prog tgt (ss.toState b env s0 m) post oom := by
  unfold step at hstep
  split at hstep
  · rename_i o hpc
    split at hstep
    · rename_i si cur'' hi
      obtain ⟨hf, hcur''⟩ := fetchCur_sound htbl hcur hi
      cases hst : stepSymInsn base ss si h with
      | none => rw [hst] at hstep; cases hstep
      | some r =>
        rw [hst] at hstep
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        obtain ⟨m', hex, hm', hlen', hvval'⟩ :=
          stepSymInsn_sound (b := b) (s0 := s0) hbase hpc hlen hvval hst hobl hm
        refine reaches_pc_step (inst := si.toInstr env (b + o)) (SState.toState_status ss) ?_ ?_
        · rw [SState.toState_pc, hpc]; exact hf
        · rw [hex]; exact hnext m' hm' hlen' hvval' hcur''
    · cases hstep
  · cases hstep

theorem runC_sound {base : SExpr} (hbase : base.eval env = b) (htbl : TblOK prog b env tbl)
    {s0 : State} {R : SepProp} {tgt : BitVec 64} {post oom : State → Prop} :
    ∀ {cur : Tbl} {hints : List Hint} {ss ssF : SState} {obl : List SProp} {m : Memory},
      TblOK prog b env cur → ss.regs.length = 31 → VRegsValid ss.vregs →
      runC base tbl cur hints ss = some (ssF, obl) →
      allHold env obl → (m ⊨ cellsProp env ss.cells ∗ R) →
      (∀ m', (m' ⊨ cellsProp env ssF.cells ∗ R) → reaches_pc prog tgt (ssF.toState b env s0 m') post oom) →
      reaches_pc prog tgt (ss.toState b env s0 m) post oom
  | _, [], ss, ssF, obl, m, _, _, _, hrun, _, hm, hnext => by
    simp only [runC, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact hnext m hm
  | cur, h :: hs, ss, ssF, obl, m, hcur, hlen, hvval, hrun, hobl, hm, hnext => by
    unfold runC at hrun
    split at hrun
    · rename_i ss1 o1 cur' hst
      split at hrun
      · rename_i ss2 o2 hr
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        rw [allHold_append] at hobl
        exact step_sound hbase htbl hcur hlen hvval hst hobl.1 hm fun m' hm' hlen' hvval' hcur' =>
          runC_sound hbase htbl hcur' hlen' hvval' hr hobl.2 hm' hnext
      · cases hrun
    · cases hrun

theorem run_sound {base : SExpr} (hbase : base.eval env = b) (htbl : TblOK prog b env tbl)
    {s0 : State} {R : SepProp} {tgt : BitVec 64}
    {post oom : State → Prop} {hints : List Hint} {ss ssF : SState} {obl : List SProp} {m : Memory}
    (hlen : ss.regs.length = 31) (hvval : VRegsValid ss.vregs)
    (hrun : run base tbl hints ss = some (ssF, obl))
    (hobl : allHold env obl) (hm : m ⊨ cellsProp env ss.cells ∗ R)
    (hnext : ∀ m', (m' ⊨ cellsProp env ssF.cells ∗ R) →
      reaches_pc prog tgt (ssF.toState b env s0 m') post oom) :
    reaches_pc prog tgt (ss.toState b env s0 m) post oom :=
  runC_sound hbase htbl htbl hlen hvval hrun hobl hm hnext

/-- Multi-step concrete execution witness (`Steps`) for `runC`, preserving `prog.CodeLoaded`. -/
theorem runC_steps {base : SExpr} (hbase : base.eval env = b) (htbl : TblOK prog b env tbl)
    {s0 : State} {R : SepProp} :
    ∀ {cur : Tbl} {hints : List Hint} {ss ssF : SState} {obl : List SProp} {m : Memory},
      TblOK prog b env cur → ss.regs.length = 31 → VRegsValid ss.vregs →
      runC base tbl cur hints ss = some (ssF, obl) →
      allHold env obl → (m ⊨ cellsProp env ss.cells ∗ R) → prog.CodeLoaded m →
      ∃ m', Steps prog (ss.toState b env s0 m) (ssF.toState b env s0 m') ∧
        (m' ⊨ cellsProp env ssF.cells ∗ R)
  | _, [], ss, ssF, obl, m, _, _, _, hrun, _, hm, _ => by
    simp only [runC, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨m, Steps.refl _, hm⟩
  | cur, h :: hs, ss, ssF, obl, m, hcur, hlen, hvval, hrun, hobl, hm, hL => by
    unfold runC at hrun
    split at hrun
    · rename_i ss1 o1 cur' hst
      split at hrun
      · rename_i ss2 o2 hr
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        rw [allHold_append] at hobl
        unfold step at hst
        split at hst
        · rename_i o hpc
          split at hst
          · rename_i si cur'' hi
            obtain ⟨hf, hcur''⟩ := fetchCur_sound htbl hcur hi
            cases hsi : stepSymInsn base ss si h with
            | none => rw [hsi] at hst; cases hst
            | some r =>
              rw [hsi] at hst
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
              obtain ⟨rfl, rfl⟩ := hst
              obtain ⟨m1, hex1, hm1, hlen1, hvval1⟩ :=
                stepSymInsn_sound (b := b) (s0 := s0) hbase hpc hlen hvval hsi hobl.1 hm
              have hfetch : prog.fetchMem (ss.toState b env s0 m).mem (ss.toState b env s0 m).pc =
                  some (si.toInstr env (b + o)) := by
                rw [SState.toState_mem, SState.toState_pc, hpc]
                exact Program.fetchMem_of_fetch hL hf
              have hstep1 : Step prog (ss.toState b env s0 m) (ss1.toState b env s0 m1) := by
                rw [← hex1]
                exact Step.exec (SState.toState_status ss) hfetch
              have hL1 : prog.CodeLoaded m1 := by
                have hcl := hstep1.codeLoaded (by rw [SState.toState_mem]; exact hL)
                simpa only [SState.toState_mem] using hcl
              obtain ⟨m', hsteps2, hm'⟩ :=
                runC_steps hbase htbl hcur'' hlen1 hvval1 hr hobl.2 hm1 hL1
              exact ⟨m', Steps.step hstep1 hsteps2, hm'⟩
          · cases hst
        · cases hst
      · cases hrun
    · cases hrun

end Soundness

/-! ## Initial state -/

/-- `regs[k]` denotes `x(i+k)` of `s`. -/
def RegsAgree (s : State) (env : Env) : Nat → List SExpr → Prop
  | _, [] => True
  | i, e :: es => s.readReg64 (.gpr (BitVec.ofNat 5 i)) = e.eval env ∧ RegsAgree s env (i + 1) es

theorem RegsAgree.get {s : State} {env : Env} :
    ∀ {i : Nat} {l : List SExpr}, RegsAgree s env i l → ∀ k, k < l.length →
      s.readReg64 (.gpr (BitVec.ofNat 5 (i + k))) = (l.getD k (.const 0)).eval env
  | _, [], _, k, hk => absurd hk (by simp)
  | _, _ :: _, h, 0, _ => by simpa using h.1
  | i, _ :: es, h, k + 1, hk => by
    have := RegsAgree.get h.2 k (by simp at hk; omega)
    rw [show i + (k + 1) = i + 1 + k by omega]
    simpa using this

/-- `vregs[k]` denotes `v(i+k)` of `s`. -/
def VRegsAgree (s : State) (env : Env) : Nat → List VExpr → Prop
  | _, [] => True
  | i, e :: es => s.readVReg128 (BitVec.ofNat 5 i) = e.eval env ∧ VRegsAgree s env (i + 1) es

theorem VRegsAgree.get {s : State} {env : Env} :
    ∀ {i : Nat} {l : List VExpr}, VRegsAgree s env i l → ∀ k, k < l.length →
      s.readVReg128 (BitVec.ofNat 5 (i + k)) = (l.getD k (.const 0)).eval env
  | _, [], _, k, hk => absurd hk (by simp)
  | _, _ :: _, h, 0, _ => by simpa using h.1
  | i, _ :: es, h, k + 1, hk => by
    have := VRegsAgree.get h.2 k (by simp at hk; omega)
    rw [show i + (k + 1) = i + 1 + k by omega]
    simpa using this

theorem toState_self {ss : SState} {b : BitVec 64} {env : Env} {s : State}
    (hregs : RegsAgree s env 0 ss.regs) (hlen : ss.regs.length = 31)
    (hvregs : VRegsAgree s env 0 ss.vregs) (hvval : VRegsValid ss.vregs)
    (hsp : ss.sp.eval env = s.sp) (htpidr : ss.tpidr.eval env = s.tpidrEl0)
    (hpc : ss.pc.denote b env = s.pc) (hfl : ss.flags = .orig)
    (hrun : s.status = .Running) : ss.toState b env s s.mem = s := by
  have hR : ∀ j : BitVec 5,
      (if j = 31#5 then s.regs.regs j else (ss.reg j.toNat).eval env) = s.regs.regs j := by
    intro j
    by_cases hj : j = 31#5
    · simp [hj]
    · have hlt : j.toNat < 31 := by
        have := j.isLt
        have : j.toNat ≠ 31 := fun h => hj (BitVec.eq_of_toNat_eq (by simpa using h))
        omega
      have := hregs.get j.toNat (by omega)
      simp only [Nat.zero_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, State.readReg64] at this
      simp only [hj, ite_false, SState.reg]
      rw [← this]
      simp [hj, RegFile.read]
  have hVR : ∀ j : BitVec 5,
      (match ss.vregs[j.toNat]? with | some ve => ve.eval env | none => s.vregs.regs j) =
        s.vregs.regs j := by
    intro j
    rcases hvval with hemp | hvlen
    · simp [hemp]
    · have hlt : j.toNat < ss.vregs.length := by omega
      have hget := hvregs.get j.toNat hlt
      simp only [Nat.zero_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, State.readVReg128,
        VRegFile.read, List.getD_eq_getElem?_getD] at hget
      rw [List.getElem?_eq_getElem hlt] at hget ⊢
      exact hget.symm
  unfold SState.toState
  cases s with
  | mk regs vregs sp pc pstate mem tpidrEl0 fpsr brkStart brk fs oracle oracleIdx exclFails trace status symtab sigActions physMemAvail =>
    congr 1
    · cases regs with | mk f => congr 1; funext j; exact hR j
    · cases vregs with | mk f => congr 1; funext j; exact hVR j
    · exact hfl ▸ rfl
    · exact hrun.symm

/-! ## The block rule -/

/-- If the reflective checker `run` accepts the hint list from the symbolic state `ss0` (which
    denotes `s` and whose cells equal `P`) and all residual obligations hold, then `SepWP` from `s`
    follows from `SepWP` from the final symbolic state `ssF` for every memory reached. -/
theorem SepWP_block {prog : Program} {tgt b : BitVec 64} {env : Env} {tbl : Tbl}
    {hints : List Hint} {ss0 ssF : SState} {obl : List SProp} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {base : SExpr} (hbase : base.eval env = b)
    (htbl : TblOK prog b env tbl) (hlen : ss0.regs.length = 31) (hvval : VRegsValid ss0.vregs)
    (hs : ss0.toState b env s s.mem = s) (hP : P = cellsProp env ss0.cells)
    (hrun : run base tbl hints ss0 = some (ssF, obl)) (hobl : allHold env obl)
    (hnext : ∀ m, SepWP prog tgt (ssF.toState b env s m) (cellsProp env ssF.cells) post oom) :
    SepWP prog tgt s P post oom := by
  unfold SepWP at hnext ⊢
  intro R hm
  subst hP
  have key := run_sound (s0 := s) (R := R) (tgt := tgt)
    (post := fun sf => ∃ P_f : SepProp, (sf.mem ⊨ P_f ∗ R) ∧ post sf P_f)
    (oom := fun sf => sf.mem ⊨ oom sf ∗ R)
    hbase htbl hlen hvval hrun hobl hm (fun m' hm' => hnext m' R (by rw [SState.toState_mem]; exact hm'))
  rw [hs] at key
  exact key

/-- Panic-aware variant of `SepWP_block` for `SepWPp` goals. -/
theorem SepWPp_block {prog : Program} {ret b : BitVec 64} {env : Env} {tbl : Tbl}
    {hints : List Hint} {ss0 ssF : SState} {obl : List SProp} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} {base : SExpr}
    (hbase : base.eval env = b) (htbl : TblOK prog b env tbl) (hlen : ss0.regs.length = 31)
    (hvval : VRegsValid ss0.vregs) (hs : ss0.toState b env s s.mem = s)
    (hP : P = cellsProp env ss0.cells) (hrun : run base tbl hints ss0 = some (ssF, obl))
    (hobl : allHold env obl)
    (hnext : ∀ m, SepWPp prog ret (ssF.toState b env s m) (cellsProp env ssF.cells) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  unfold SepWPp at hnext ⊢
  intro R hm hL
  subst hP
  obtain ⟨m1, hsteps1, hm1⟩ :=
    runC_steps (s0 := s) (R := R) hbase htbl htbl hlen hvval hrun hobl hm hL
  rw [hs] at hsteps1
  have hL1 : prog.CodeLoaded (ssF.toState b env s m1).mem := hsteps1.codeLoaded hL
  obtain ⟨sf, hsteps2, hpost⟩ := hnext m1 R (by rw [SState.toState_mem]; exact hm1) hL1
  exact ⟨sf, hsteps1.trans hsteps2, hpost⟩

end ProofLib.SymBlock
