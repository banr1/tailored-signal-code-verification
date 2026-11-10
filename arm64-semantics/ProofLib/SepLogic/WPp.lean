/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.CFG
public import ProofLib.ObjectLoad
public import ProofLib.Hoare.Hooks
public import ProofLib.SepLogic.CodeLookup
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model

/-!
# Panic-Aware Separation-Logic Weakest Preconditions

Provides proof rules, loop and CFG combinators (`SepWPp.loop_wf`, `SepWPp.loop_nat_cps`,
`SepWPp.loop_list_peel_cps`, `SepWPp.cfg_fixpoint_wf_cps`), entry setup (`wpp_init`),
and instruction-fetch tactics (`code_fetches`, `code_fetches_range`, `code_fetches_fn`)
for the panic-aware weakest precondition `SepWPp`.
-/

namespace ProofLib

open Arm64

@[expose] public section

/-- Normalize `x - a + b` to `x - (a - b)` for literals `b < a` (stack-slot addresses). -/
theorem bv_sub_add_lit (x : BitVec 64) (a b : Nat) (h : b < a := by decide)
    (ha : a < 2 ^ 64 := by decide) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have : b % 2 ^ 64 = b := Nat.mod_eq_of_lt (by omega)
  have : a % 2 ^ 64 = a := Nat.mod_eq_of_lt ha
  have : (a - b) % 2 ^ 64 = a - b := Nat.mod_eq_of_lt (by omega)
  simp only [*]
  omega

/-- Fold part `T` of the spatial context into `T'` (`T` is found by `sep_focus`). -/
theorem SepWP.fold {prog : Program} {pc : BitVec 64} {s : State} {P T T' F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} (hent : T ⊢ T') (hf : P = T ∗ F)
    (h : SepWP prog pc s (T' ∗ F) post oom) : SepWP prog pc s P post oom :=
  SepWP.weaken_pre (hf ▸ sepConj_mono_left hent) h

namespace SepWPp

variable {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
  {Q Qp : State → SepProp → Prop} {oom : State → SepProp}

/-- Run a `SepWP` segment to `mid`; at `mid`, a `KeepsFrozen`-stable fact `Φ` that held for
    `s.mem` holds again for `sm.mem`, and the proof continues with `SepWPp` to `ret`. -/
theorem seq_frozen {mid : BitVec 64} {Φ : Memory → Prop}
    (hst : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m') (hΦ : Φ s.mem)
    (h : SepWP prog mid s P (fun sm Pm => Φ sm.mem → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hcont (hst _ _ hΦ hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

/-- At an extern whose hook is `Rust.panicked`: the program panics with memory unchanged. -/
theorem panic (hrun : s.status = .Running) (hext : prog.externAt? s.pc = some Rust.panicked)
    (hqp : Qp (Rust.panicked s) P) : SepWPp prog ret s P Q Qp oom := by
  intro R hm _
  refine ⟨Rust.panicked s, Steps.step (Step.extern hrun hext (Memory.KeepsFrozen.refl _)) (Steps.refl _),
    Or.inr (Or.inl ⟨rfl, P, hm, hqp⟩)⟩

end SepWPp

/-- `subroutine_ok` for a spec that may panic, from `SepWPp` at entry. On return the final
    context must entail `spec.post` with calling conventions preserved; on panic it must
    entail `spec.onPanic`. -/
theorem subroutine_ok_of_sepWPp {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPp prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry spec := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  rw [reaches_outcome_iff]
  intro hL
  obtain ⟨P, Fr, hm, hwp⟩ := h x R s0 hpc hrun hpre hsp
  obtain ⟨sf, hsteps, hout⟩ := hwp Fr hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hq, hspf, hcsf⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hmo⟩
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, hq hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hqp hmf⟩)⟩
  · exact (not_satisfies_false_sepConj hmo).elim

/-- `subroutine_ok` for a spec that may panic (and may OOM via `spec.onOom`), from `SepWPp` at
    entry with caller frame `R`. Used by `wpp_init`. -/
theorem subroutine_ok_of_sepWPp_init {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P : SepProp, (s0.mem ⊨ P ∗ R) ∧
        SepWPp prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))
          (fun sf => spec.onOom x s0 sf)) :
    subroutine_ok prog entry spec := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  rw [reaches_outcome_iff]
  intro hL
  obtain ⟨P, hm, hwp⟩ := h x R s0 hpc hrun hpre hsp
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hq, hspf, hcsf⟩ | ⟨hpan, P_f, hmf, hqp⟩ | hoom
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, hq hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hqp hmf⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr hoom))⟩

/-- Derive `subroutine_ok` from `SepWPp` with a split local frame `F0 ∗ R` and pure
    `spec.onOom x s0 sf = ⌜φ x s0 sf⌝`, dropping `F0` on `.OutOfMemory` via `Satisfies.drop_left`. -/
theorem subroutine_ok_of_sepWPp_pure_oom {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {φ : α → State → State → Prop}
    (hoom_eq : ∀ x s0 sf, spec.onOom x s0 sf = ⌜φ x s0 sf⌝ := by intros; rfl)
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P F0 : SepProp, (s0.mem ⊨ P ∗ (F0 ∗ R)) ∧
        SepWPp prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ (F0 ∗ R)) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ (F0 ∗ R)) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))
          (fun sf => ⌜φ x s0 sf⌝)) :
    subroutine_ok prog entry spec := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  rw [reaches_outcome_iff]
  intro hL
  obtain ⟨P, F0, hm, hwp⟩ := h x R s0 hpc hrun hpre hsp
  obtain ⟨sf, hsteps, hout⟩ := hwp (F0 ∗ R) hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hq, hspf, hcsf⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨ho, hmo⟩
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, hq hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hqp hmf⟩)⟩
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))⟩
    rw [satisfies_pure_sepConj] at hmo
    rw [hoom_eq x s0 sf, satisfies_pure_sepConj]
    exact ⟨hmo.1, Satisfies.drop_left hmo.2⟩

end

public meta section

open Lean Elab Tactic Meta in
/-- `wpp_init x s0`: like `wp_init x s0`, but for a spec that may panic, reducing
    `subroutine_ok` to a `SepWPp` goal via `subroutine_ok_of_sepWPp_init` (the spatial context is the
    spatial part of the precondition, the frame is `R`). -/
elab "wpp_init " a:ident s0:ident : tactic => do
  wpUnfoldProgAbbrs
  let rId := mkIdent `R
  let hpcId := mkIdent `hpc
  let hrunId := mkIdent `hrun
  let hpreId := mkIdent `hpre
  let hspId := mkIdent `hsp_align
  let _ ← tryTactic (evalTactic (← `(tactic|
    dsimp only [Program.relocSubroutineOk, Program.alignedSubroutineOk,
      Obj.LinkedImage.subroutineOk, Program.subroutineOk, fn_subroutine_ok,
      ToBaseSpec.toSpec, instToBaseSpecId, instToBaseSpecFn, wp_proj_guard])))
  evalTactic (← `(tactic| (
    wp_unfold_specs
    apply subroutine_ok_of_sepWPp_init
    intro $a:ident $rId:ident $s0:ident $hpcId:ident $hrunId:ident $hpreId:ident $hspId:ident
    try simp only [stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def, wp_proj_guard] at $hpreId:ident)))
  wpSplitAndNormHyps (unpackProds := false)
  let g ← getMainGoal
  let pExpr ← g.withContext do
    let lctx ← getLCtx
    let rFVar := (lctx.findFromUserName? rId.getId).map (·.toExpr)
    let mut fullPreOpt : Option Expr := none
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← instantiateMVars decl.type
        if ty.isAppOfArity ``SepProp.Satisfies 2 then
          fullPreOpt := some (ty.getArg! 0)
          break
    let fullPre := fullPreOpt.getD (rFVar.getD (mkConst ``SepProp.emp))
    let atoms := SepSolver.atoms fullPre
    let spatial := atoms.filter (fun (e : Expr) => rFVar != some e)
    let conj : Expr :=
      if spatial.isEmpty then mkConst ``SepProp.emp
      else
        let n := spatial.size
        (List.range (n - 1)).foldr
          (fun i acc => mkApp2 (mkConst ``SepProp.sepConj) spatial[i]! acc) spatial[n - 1]!
    Pure.pure conj
  let pStx ← g.withContext do Term.exprToSyntax (← instantiateMVars pExpr)
  evalTactic (← `(tactic| (
    refine ⟨$pStx, ?_, ?_⟩
    wp_focus_close arm64_sep_close)))
  (← getGoals).forM instantiateMVarDeclMVars

end

@[expose] public section

/-! ## `Spec.allowPanicWhen` (`⌜φ⌝ ∗ anyHeap`) postcondition helpers -/

/-- Close the panic path at a panicking extern (`hext`) for an `onPanic` of the form `⌜φ⌝ ∗ anyHeap`. -/
theorem SepWPp.panic_allowPanic {prog : Program} {ret : BitVec 64} {s : State} {P R : SepProp}
    {Q : State → SepProp → Prop} {oom : State → SepProp} {φ : Prop}
    (hrun : s.status = .Running) (hext : prog.externAt? s.pc = some Rust.panicked) (hφ : φ) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜φ⌝ ∗ anyHeap) ∗ R)) oom :=
  SepWPp.panic hrun hext fun h => allowPanic_panicked hφ h

@[deprecated SepWPp.panic_allowPanic (since := "2026-10-25")]
abbrev SepWPp.panic_panicsOr := @SepWPp.panic_allowPanic

/-- `SepWPp.panic_allowPanic` at a named panicking extern `target`, for an `onPanic` of the
    flattened form `⌜φ⌝ ∗ anyHeap ∗ R`. The `pc`/`status` side conditions are discharged by
    `wp_norm_lhs` by default, so a call site only supplies the extern fact and `φ`. -/
theorem SepWPp.panic_allowPanic_at {prog : Program} {ret target : BitVec 64} {s : State}
    {P R : SepProp} {Q : State → SepProp → Prop} {oom : State → SepProp} {φ : Prop}
    (hext : prog.externAt? target = some Rust.panicked) (hφ : φ)
    (hrun : s.status = .Running := by wp_norm_lhs)
    (hpc : s.pc = target := by wp_norm_lhs) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜φ⌝ ∗ anyHeap ∗ R)) oom :=
  SepWPp.panic hrun (hpc ▸ hext) fun h => by
    rw [← sepConj_assoc]
    exact allowPanic_panicked hφ h

/-- Extract a leading pure conjunct `⌜φ⌝ ∗ P` from the precondition of `SepWPp`. -/
theorem SepWPp.pure_left {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp oom := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL


/-- Permute the precondition of `SepWPp` using `sep_focus` (`hf : P = P' ∗ emp`). -/
theorem SepWPp.perm {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp prog ret s P' Q Qp oom)
    (hf : P = P' ∗ emp := by sep_focus) :
    SepWPp prog ret s P Q Qp oom := by
  rw [hf, sepConj_emp]
  exact h


/-- Rewrite the precondition of `SepWPp` along an equality `hP : P = P'`. -/
theorem SepWPp.congr_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P = P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  hP ▸ h

/-- Strengthen a state-indexed spatial postcondition entailment `Pm ⊢ Q₁ sm` to `Pm ⊢ Q₂ sm`
    in `SepWPp`, preserving panic (`Qp`) and out-of-memory (`oom`) outcomes. -/
theorem SepWPp.strengthen_entails {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q₁ Q₂ : State → SepProp} {φ : State → Prop}
    {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (himp : ∀ sm, Q₁ sm ⊢ Q₂ sm)
    (h : SepWPp prog ret s P (fun sm Pm => (Pm ⊢ Q₁ sm) ∧ φ sm) Qp oom) :
    SepWPp prog ret s P (fun sm Pm => (Pm ⊢ Q₂ sm) ∧ φ sm) Qp oom := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, h1, h2⟩ | hpan | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, Entails.trans h1 (himp sf), h2⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-- Constant-spatial specialization of `SepWPp.strengthen_entails`. -/
theorem SepWPp.strengthen_entails_const {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ : SepProp} {φ : State → Prop}
    {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (himp : P₁ ⊢ P₂)
    (h : SepWPp prog ret s P (fun sm Pm => (Pm ⊢ P₁) ∧ φ sm) Qp oom) :
    SepWPp prog ret s P (fun sm Pm => (Pm ⊢ P₂) ∧ φ sm) Qp oom :=
  SepWPp.strengthen_entails (fun _ => himp) h



/-- Call a `subroutine_ok` callee that may panic (`Qpan`), and continue after `ret_pc` with a
    non-panicking `SepWP` proof to `target_pc`. -/
theorem SepWPp.call_allowPanic_ret {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R Qpan : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → s.mem.KeepsFrozen sf.mem →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan ∗ R)) oom := by
  intro R' hm hL
  obtain ⟨sm, hsteps, hout⟩ :=
    reaches_outcome_iff.1
      (subroutine_ok_apply_outcome hcall x (F ∗ R') hpc hrun (hpre R' hm) hsp_align) hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      (SepWPp.of_sepWP_ret (hnext sm hpcm hrunm hspm hcsm hsteps.keepsFrozen))
        R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · rw [hexit_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_st, hoom sm R' hoom_st hpost⟩)⟩

/-! ## Local Context Fetch Hypotheses and Entry Generalization Tactics -/

theorem fetch_eq_of_entry_eq_add {prog : Program} {e entry k : BitVec 64} {r : Option Instr}
    (he : e = entry) (h : prog.fetch (e + k) = r) : prog.fetch (entry + k) = r :=
  he ▸ h

end

public meta section

open Lean Meta Elab Tactic in
private def addCodeFetchesRange (codeId decPrefix : Ident) (b H : Term) (hfn : Ident)
    (off start len : Nat) : TacticM Unit := do
  let n := len / 4
  if n == 0 then return
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  if start == 0 then
    let dec0 := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 off)}")
    evalTactic (← `(tactic|
      have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec0))
  let i0 := if start == 0 then 1 else 0
  if n <= i0 then return
  let k0 := start + 4 * i0
  let dec0Add := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k0))}")
  let k0q := Syntax.mkNumLit (toString k0)
  let stx0 ← `($fetchAdd (b := $b) (H := $H) (k := $k0q) $hfn (by decide) $dec0Add)
  let g ← getMainGoal
  let fastOk ← g.withContext do
    tryCatchRuntimeEx (do
      let e4 ← instantiateMVars (← Term.elabTermAndSynthesize stx0 none)
      let ty4 ← instantiateMVars (← inferType e4)
      let fn := e4.getAppFn
      let args := e4.getAppArgs
      if args.size == 10 && ty4.isAppOfArity ``Eq 3 && (ty4.getArg! 1).isAppOfArity ``Program.fetch 2 then
        let offExpr := args[3]!
        let textEndExpr := (args[7]!.getArg! 0).getArg! 3
        let pow64Expr := (args[9]!.getArg! 0).getArg! 3
        let natTy := mkConst ``Nat
        let instLTNatE := mkConst ``instLTNat
        let hAddNatFn := mkApp4 (mkConst ``HAdd.hAdd [0, 0, 0]) natTy natTy natTy
          (mkApp2 (mkConst ``instHAdd [0]) natTy (mkConst ``instAddNat))
        let reflTrue := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
        let mkDecLtProof (kExpr boundExpr : Expr) : Expr :=
          let sumE := mkApp2 hAddNatFn offExpr kExpr
          let propE := mkApp4 (mkConst ``LT.lt [0]) natTy instLTNatE sumE boundExpr
          let instE := mkApp2 (mkConst ``Nat.decLt) sumE boundExpr
          mkApp3 (mkConst ``of_decide_eq_true) propE instE reflTrue
        let optInstrTy := ty4.getArg! 0
        let fetchLhs4 := ty4.getArg! 1
        let progExpr := fetchLhs4.getArg! 0
        let addAddr4 := fetchLhs4.getArg! 1
        let addPrefix := addAddr4.appFn!
        let bvOfNatPrefix := (addAddr4.getArg! 5).appFn!
        let env ← getEnv
        let mut hyps : Array Hypothesis := #[{ userName := `this, type := ty4, value := e4 }]
        for i in [i0 + 1 : n] do
          let k := start + 4 * i
          let decName := decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}"
          let some info := env.find? decName | return false
          let someInstExpr := info.type.getArg! 2
          let instExpr := someInstExpr.getArg! 1
          let kExpr := mkNatLit k
          let valK := mkApp10 fn args[0]! args[1]! args[2]! offExpr kExpr instExpr args[6]!
            (mkDecLtProof kExpr textEndExpr) (mkConst decName) (mkDecLtProof kExpr pow64Expr)
          let tyK := mkApp3 (mkConst ``Eq [1]) optInstrTy
            (mkApp2 (mkConst ``Program.fetch) progExpr (mkApp addPrefix (mkApp bvOfNatPrefix kExpr)))
            someInstExpr
          hyps := hyps.push { userName := `this, type := tyK, value := valK }
        let (_, g') ← g.assertHypotheses hyps
        replaceMainGoal [g']
        return true
      else
        return false
    ) (fun _ => pure false)
  if !fastOk then
    for i in [i0 : n] do
      let k := start + 4 * i
      let dec := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
      let kq := Syntax.mkNumLit (toString k)
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

open Lean Elab Tactic in
/-- `code_fetches <code> <decPrefix> b H hfn off len` adds `<code>_fetch_fnAddr` hypotheses for the
    instructions `k = 0, 4, ..., len - 4` of the function at offset `off`
    (`hfn : <code>.fnOff name = off`), using `<decPrefix>_decode_0x<off+k>`. -/
elab "code_fetches " codeId:ident decPrefix:ident b:term:max H:term:max hfn:ident
    off:num len:num : tactic =>
  addCodeFetchesRange codeId decPrefix b H hfn off.getNat 0 len.getNat

open Lean Elab Tactic in
/-- `code_fetches_range <code> <decPrefix> b H hfn off start len` adds `<code>_fetch_fnAddr`
    hypotheses for the sub-slice `k = start, start + 4, ..., start + len - 4` of a large function
    at offset `off` (`hfn : <code>.fnOff name = off`), avoiding polluting the local context with
    fetch hypotheses from unvisited basic blocks. -/
elab "code_fetches_range " codeId:ident decPrefix:ident b:term:max H:term:max hfn:ident
    off:num start:num len:num : tactic =>
  addCodeFetchesRange codeId decPrefix b H hfn off.getNat start.getNat len.getNat

open Lean Elab Tactic in
/-- `code_fetches_fn <code> <decPrefix> b H "<sym>"` is `code_fetches` for function `sym`, with
    its `fnOff` lemma, offset, and size looked up by name (`ProofLib.CodeLookup`), so the proof is
    independent of where the linker placed `sym`.
    `code_fetches_fn <code> <decPrefix> b H "<sym>" start len` fetches only the sub-slice
    `k = start, ..., start + len - 4` (like `code_fetches_range`). -/
syntax "code_fetches_fn " ident ident term:max term:max str (num num)? : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| code_fetches_fn $codeId:ident $decPrefix:ident $b $H $sym:str $[$st:num $ln:num]?) => do
    let codeName ← realizeGlobalConstNoOverloadWithInfo codeId
    let eOff ← CodeLookup.lookup codeName .fnOff sym.getString
    let eSize ← CodeLookup.lookup codeName .fnSize sym.getString
    let hfn := mkCIdentFrom sym eOff.decl
    let (start, len) := match st, ln with
      | some s, some l => (s.getNat, l.getNat)
      | _, _ => (0, eSize.val)
    addCodeFetchesRange (mkCIdent codeName) decPrefix b H hfn eOff.val start len

open Lean Meta Elab Tactic in
/-- `examples_generalize_entry` (run after `wp_init`) replaces the entry address
    `prog.fnAddr name` in the goal and every hypothesis by a fresh opaque variable `entry`. -/
elab "examples_generalize_entry" : tactic => do
  let g0 ← getMainGoal
  let (found?, hpcLhs?) ← g0.withContext do
    let mut fetchFnAddr? : Option Expr := none
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail && fetchFnAddr?.isNone then
        let ty ← instantiateMVars decl.type
        if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``Program.fetch 2 then
          let addr := (ty.getArg! 1).getArg! 1
          if addr.isAppOfArity ``HAdd.hAdd 6 && (addr.getArg! 4).isAppOfArity ``Program.fnAddr 2 then
            fetchFnAddr? := some (addr.getArg! 4)
    let tgt ← instantiateMVars (← g0.getType)
    let mut found? := fetchFnAddr?.orElse (fun _ => tgt.find? (·.isAppOfArity ``Program.fnAddr 2))
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        let ty ← instantiateMVars decl.type
        if found?.isNone then
          found? := ty.find? (·.isAppOfArity ``Program.fnAddr 2)
    let mut hpcLhs? : Option Expr := none
    if let some e := found? then
      if let some decl := (← getLCtx).findFromUserName? `hpc then
        if let some (_, lhs, rhs) := (← instantiateMVars decl.type).eq? then
          if rhs != e then
            hpcLhs? := some lhs
    pure (found?, hpcLhs?)
  let some e := found? | throwError "examples_generalize_entry: no `Program.fnAddr` term found"
  if let some lhs := hpcLhs? then
    let lhsStx ← g0.withContext do Term.exprToSyntax (← instantiateMVars lhs)
    let eStx ← g0.withContext do Term.exprToSyntax (← instantiateMVars e)
    let hpcId := mkIdent `hpc
    let htmpId := mkIdent `_hpc_entry_tmp
    evalTactic (← `(tactic| (
      have $htmpId:ident : $lhsStx = $eStx := Eq.trans $hpcId:ident (by
        simp (config := { decide := true }) only [Program.fnAddr_rebase, wp_norm, arm64_norm])
      clear $hpcId:ident
      have $hpcId:ident := $htmpId:ident
      clear $htmpId:ident)))
    (← getGoals).forM instantiateMVarDeclMVars
  let g ← getMainGoal
  g.withContext do
    let mut otherHyps : Array FVarId := #[]
    let mut fetchAddHyps : Array (FVarId × Name × Expr × Expr × Expr × Expr × Expr) := #[]
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        let ty ← instantiateMVars decl.type
        let hasValE ← match decl.value? with
          | some v => pure ((← instantiateMVars v).find? (·.isAppOfArity ``Program.fnAddr 2)).isSome
          | none => pure false
        if !hasValE && ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``Program.fetch 2 then
          let optInstrTy := ty.getArg! 0
          let lhs := ty.getArg! 1
          let rhs := ty.getArg! 2
          let prog := lhs.getArg! 0
          let addr := lhs.getArg! 1
          if addr.isAppOfArity ``HAdd.hAdd 6 && addr.getArg! 4 == e &&
             (prog.find? (·.isAppOfArity ``Program.fnAddr 2)).isNone &&
             ((addr.getArg! 5).find? (·.isAppOfArity ``Program.fnAddr 2)).isNone &&
             (rhs.find? (·.isAppOfArity ``Program.fnAddr 2)).isNone then
            fetchAddHyps := fetchAddHyps.push (decl.fvarId, decl.userName, optInstrTy, prog, addr.appFn!.appFn!, addr.getArg! 5, rhs)
          else
            otherHyps := otherHyps.push decl.fvarId
        else
          otherHyps := otherHyps.push decl.fvarId
    if fetchAddHyps.isEmpty then
      let (_, _, g') ← g.generalizeHyp #[{ expr := e, xName? := some `entry }] otherHyps
      replaceMainGoal [g']
    else
      let (_, genFVars, g1) ← g.generalizeHyp #[{ expr := e, xName? := some `entry, hName? := some `_hentry }] otherHyps
      if h : genFVars.size = 2 then
        let entryE := mkFVar genFVars[0]
        let hentryE := mkFVar genFVars[1]
        let mut newHyps : Array Hypothesis := #[]
        let mut oldFVars : Array FVarId := #[]
        for (fid, uName, optInstrTy, prog, addFnPrefix, kBv, rhs) in fetchAddHyps do
          let tyNew := mkApp3 (mkConst ``Eq [1]) optInstrTy
            (mkApp2 (mkConst ``Program.fetch) prog (mkApp2 addFnPrefix entryE kBv))
            rhs
          let valNew := mkApp7 (mkConst ``fetch_eq_of_entry_eq_add) prog e entryE kBv rhs hentryE (mkFVar fid)
          newHyps := newHyps.push { userName := uName, type := tyNew, value := valNew }
          oldFVars := oldFVars.push fid
        let (_, g2) ← g1.assertHypotheses newHyps
        let g3 ← g2.tryClearMany (oldFVars.push genFVars[1])
        replaceMainGoal [g3]
      else
        throwError "examples_generalize_entry: unexpected generalized variable count {genFVars.size} (expected 2)"

open Lean Meta Elab Tactic in
/-- `examples_clear_fetches` clears every hypothesis `prog.fetch a = i`. -/
elab "examples_clear_fetches" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut fvs : Array FVarId := #[]
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        if let some (_, lhs, _) := (← instantiateMVars decl.type).eq? then
          if lhs.isAppOfArity ``Program.fetch 2 then fvs := fvs.push decl.fvarId
    replaceMainGoal [← g.tryClearMany fvs]

open Lean Meta Elab Tactic in
/-- `examples_hide_fetches` marks every hypothesis `prog.fetch a = i` as an implementation detail. -/
elab "examples_hide_fetches" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut lctx ← getLCtx
    for decl in lctx do
      if !decl.isImplementationDetail then
        if let some (_, lhs, _) := (← instantiateMVars decl.type).eq? then
          if lhs.isAppOfArity ``Program.fetch 2 then
            lctx := lctx.setKind decl.fvarId .implDetail
    let g' ← mkFreshExprMVarAt lctx (← getLocalInstances) (← g.getType) .syntheticOpaque (← g.getTag)
    g.assign g'
    replaceMainGoal [g'.mvarId!]

/-! ## Panic-Aware Loop & CFG Combinators -/

/-- Sequence a non-panicking `SepWP` block ending at `mid_pc` with `sepPost Inv1 Q1`
    into a `SepWPp` continuation targeting `target_pc`, framing `F`. -/
theorem SepWPp.bind_sepWP {prog : Program} {mid_pc target_pc : BitVec 64} {s : State}
    {P P1 Q1 F : SepProp} {Inv1 : State → Prop} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h1 : SepWP prog mid_pc s P1 (sepPost Inv1 Q1) oom)
    (hpre : P ⊢ P1 ∗ F)
    (h2 : ∀ s1 : State, s1.pc = mid_pc → s1.status = .Running → Inv1 s1 →
      SepWPp prog target_pc s1 (Q1 ∗ F) Q Qp oom) :
    SepWPp prog target_pc s P Q Qp oom := by
  intro R hm hL
  have hm' : s.mem ⊨ (P1 ∗ F) ∗ R := Satisfies.mono (sepConj_mono_left hpre) hm
  rcases (SepWP.frame_sepPost h1 (F := F)).elim hm' hL with
    ⟨s1, hsteps, ⟨hpc1, hrun1, P_m, hmm, hInv1, hent1⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      h2 s1 hpc1 hrun1 hInv1 R (Satisfies.mono (sepConj_mono_left hent1) hmm) (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨s1, hsteps, Or.inr (Or.inr hoom)⟩

/-- Panic-aware well-founded ghost-state loop combinator with a single-goal step obligation,
    state-aware measure `meas : G → State → Nat`, ghost-indexed normal postcondition `Q`, and
    uniform panic postcondition `Qp`. -/
theorem SepWPp.loop_wf {G : Type _} {prog : Program} {head_pc target_pc : BitVec 64}
    (meas : G → State → Nat)
    (P_inv : G → State → SepProp)
    (Inv : G → State → Prop)
    (Q : G → State → SepProp → Prop)
    (Qp : State → SepProp → Prop)
    {oom : State → SepProp}
    {g0 : G} {s0 : State} {P : SepProp}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv g0 s0)
    (hinv0 : Inv g0 s0)
    (hstep : ∀ (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv g st →
      (∀ (g' : G) (st' : State), meas g' st' < meas g st →
        st'.pc = head_pc → st'.status = .Running → Inv g' st' →
        SepWPp prog target_pc st' (P_inv g' st') (Q g') Qp oom) →
      SepWPp prog target_pc st (P_inv g st) (Q g) Qp oom) :
    SepWPp prog target_pc s0 P (Q g0) Qp oom := by
  intro R hm hL
  suffices h : ∀ (n : Nat) (g : G) (st : State), meas g st = n →
      st.pc = head_pc → st.status = .Running → Inv g st →
      SepWPp prog target_pc st (P_inv g st) (Q g) Qp oom from
    h (meas g0 s0) g0 s0 rfl hpc0 hrun0 hinv0 R (Satisfies.mono (sepConj_mono_left hent0) hm) hL
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro g st hn hpc hrun hinv
    refine hstep g st hpc hrun hinv ?_
    intro g' st' hlt hpc' hrun' hinv'
    exact ih (meas g' st') (hn ▸ hlt) g' st' rfl hpc' hrun' hinv'

/-- Specialization of `SepWPp.loop_wf` for loops with a ghost-independent normal exit
    postcondition `Q : State → SepProp → Prop`. -/
theorem SepWPp.loop_wf_simple {G : Type _} {prog : Program} {head_pc target_pc : BitVec 64}
    (meas : G → State → Nat)
    (P_inv : G → State → SepProp)
    (Inv : G → State → Prop)
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    {g0 : G} {s0 : State} {P : SepProp}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv g0 s0)
    (hinv0 : Inv g0 s0)
    (hstep : ∀ (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv g st →
      (∀ (g' : G) (st' : State), meas g' st' < meas g st →
        st'.pc = head_pc → st'.status = .Running → Inv g' st' →
        SepWPp prog target_pc st' (P_inv g' st') Q Qp oom) →
      SepWPp prog target_pc st (P_inv g st) Q Qp oom) :
    SepWPp prog target_pc s0 P Q Qp oom :=
  SepWPp.loop_wf meas P_inv Inv (fun _ => Q) Qp hpc0 hrun0 hent0 hinv0 hstep

/-- Apply an in-context `SepWPp` back-edge continuation `next` at `head_pc`, optionally peeling
    a spatial frame `F_peel` (defaulting to `emp`) across both `Q_cur` and `Qp`. -/
theorem SepWPp.loop_back {G : Type _} {prog : Program} {head_pc target_pc : BitVec 64}
    {meas : G → State → Nat} {P_inv : G → State → SepProp} {Inv : G → State → Prop}
    {Q : G → State → SepProp → Prop} {Q_cur Qp : State → SepProp → Prop} {oom : State → SepProp}
    {n : Nat} {st' : State} {P_cur : SepProp}
    (next : ∀ (g' : G) (st' : State), meas g' st' < n →
      st'.pc = head_pc → st'.status = .Running → Inv g' st' →
      SepWPp prog target_pc st' (P_inv g' st') (Q g') Qp oom)
    (g' : G)
    (hlt : meas g' st' < n)
    (hpc : st'.pc = head_pc) (hrun : st'.status = .Running) (hinv : Inv g' st')
    (F_peel : SepProp := emp)
    (hpre : P_cur ⊢ P_inv g' st' ∗ F_peel := by (try rw [sepConj_emp]); sep_frame)
    (hQ : ∀ sf P_f, sf.pc = target_pc → sf.status = .Running →
      Q g' sf P_f → Q_cur sf (P_f ∗ F_peel) := by
      intro sf P_f _ _ h; (try rw [sepConj_emp]); exact h)
    (hQp : ∀ sf P_p, sf.status = .Panicked → Qp sf P_p → Qp sf (P_p ∗ F_peel) := by
      intro sf P_p _ h; (try rw [sepConj_emp]); exact h)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ oom sf ∗ (F_peel ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; first | (try rw [emp_sepConj] at ho); exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj_frame ho | exact Satisfies.drop_mid ho) :
    SepWPp prog target_pc st' P_cur Q_cur Qp oom := by
  intro R hm hL
  have hm' : st'.mem ⊨ P_inv g' st' ∗ (F_peel ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hpre) hm
  obtain ⟨sf, hst, hout⟩ := next g' st' hlt hpc hrun hinv (F_peel ∗ R) hm' hL
  refine ⟨sf, hst, ?_⟩
  rcases hout with ⟨hpcf, hrunf, P1, hmf, hQ'⟩ | ⟨hpan, P1, hmp, hQp'⟩ | ⟨hoom_st, hmo⟩
  · rw [← sepConj_assoc] at hmf
    exact Or.inl ⟨hpcf, hrunf, P1 ∗ F_peel, hmf, hQ sf P1 hpcf hrunf hQ'⟩
  · rw [← sepConj_assoc] at hmp
    exact Or.inr (Or.inl ⟨hpan, P1 ∗ F_peel, hmp, hQp sf P1 hpan hQp'⟩)
  · exact Or.inr (Or.inr ⟨hoom_st, hoom sf R hoom_st hmo⟩)

/-- Panic-aware bounded counter / stride loop combinator over remaining iterations `rem : Nat`
    and evolving ghost state `g : G` in CPS form with a single-goal step obligation. -/
theorem SepWPp.loop_nat_cps {G : Type _} {prog : Program} {head_pc ret_pc : BitVec 64}
    (P_inv : Nat → G → State → SepProp)
    (Inv : Nat → G → State → Prop)
    (Q : Nat → G → State → SepProp → Prop)
    (Qp : State → SepProp → Prop)
    {oom : State → SepProp}
    {rem0 : Nat} {g0 : G} {s0 : State} {P : SepProp}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv rem0 g0 s0)
    (hinv0 : Inv rem0 g0 s0)
    (hzero : ∀ (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv 0 g st →
      SepWPp prog ret_pc st (P_inv 0 g st) (Q 0 g) Qp oom)
    (hsucc : ∀ (k : Nat) (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv (k + 1) g st →
      (∀ (g' : G) (st' : State),
        st'.pc = head_pc → st'.status = .Running → Inv k g' st' →
        SepWPp prog ret_pc st' (P_inv k g' st') (Q k g') Qp oom) →
      SepWPp prog ret_pc st (P_inv (k + 1) g st) (Q (k + 1) g) Qp oom) :
    SepWPp prog ret_pc s0 P (Q rem0 g0) Qp oom := by
  intro R hm hL
  suffices h : ∀ (rem : Nat) (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv rem g st →
      SepWPp prog ret_pc st (P_inv rem g st) (Q rem g) Qp oom from
    h rem0 g0 s0 hpc0 hrun0 hinv0 R (Satisfies.mono (sepConj_mono_left hent0) hm) hL
  intro rem
  induction rem with
  | zero => exact hzero
  | succ k ih =>
    intro g st hpc hrun hinv
    exact hsucc k g st hpc hrun hinv ih

/-- Panic-aware list-cursor loop combinator with ghost state `G`, mid-loop early exits, and
    automatic return-path spatial frame peeling across both normal and panic postconditions. -/
theorem SepWPp.loop_list_peel_cps {α G : Type _} {prog : Program} {head_pc ret_pc : BitVec 64}
    (P_inv : List α → G → State → SepProp)
    (Inv : List α → G → State → Prop)
    (Q : List α → G → State → SepProp → Prop)
    (Qp : State → SepProp → Prop)
    {oom : State → SepProp}
    {xs0 : List α} {g0 : G} {s0 : State} {P : SepProp}
    (hpc0 : s0.pc = head_pc)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv xs0 g0 s0)
    (hinv0 : Inv xs0 g0 s0)
    (hnil : ∀ (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv [] g st →
      SepWPp prog ret_pc st (P_inv [] g st) (Q [] g) Qp oom)
    (hcons : ∀ (x : α) (rest : List α) (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv (x :: rest) g st →
      (∀ (g' : G) (st' : State) {P_cur : SepProp} (F_peel : SepProp),
        st'.pc = head_pc → st'.status = .Running → Inv rest g' st' →
        (P_cur ⊢ P_inv rest g' st' ∗ F_peel) →
        (∀ sf P_f, sf.pc = ret_pc → sf.status = .Running →
          Q rest g' sf P_f → Q (x :: rest) g sf (P_f ∗ F_peel)) →
        (∀ sf P_p, sf.status = .Panicked → Qp sf P_p → Qp sf (P_p ∗ F_peel)) →
        SepWPp prog ret_pc st' P_cur (Q (x :: rest) g) Qp oom) →
      SepWPp prog ret_pc st (P_inv (x :: rest) g st) (Q (x :: rest) g) Qp oom)
    (hoom : ∀ sf F_peel R', sf.status = .OutOfMemory →
      (sf.mem ⊨ oom sf ∗ (F_peel ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ _ ho; first | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj_frame ho | exact Satisfies.drop_mid ho) :
    SepWPp prog ret_pc s0 P (Q xs0 g0) Qp oom := by
  intro R hm hL
  suffices h : ∀ (xs : List α) (g : G) (st : State),
      st.pc = head_pc → st.status = .Running → Inv xs g st →
      SepWPp prog ret_pc st (P_inv xs g st) (Q xs g) Qp oom from
    h xs0 g0 s0 hpc0 hrun0 hinv0 R (Satisfies.mono (sepConj_mono_left hent0) hm) hL
  intro xs
  induction xs with
  | nil => exact hnil
  | cons x rest ih =>
    intro g st hpc hrun hinv
    refine hcons x rest g st hpc hrun hinv ?_
    intro g' st' P_cur F_peel hpc' hrun' hinv' hpre hQ hQp R' hm' hL'
    have hm'' : st'.mem ⊨ P_inv rest g' st' ∗ (F_peel ∗ R') := by
      rw [← sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hpre) hm'
    obtain ⟨sf, hst, hout⟩ := ih g' st' hpc' hrun' hinv' (F_peel ∗ R') hm'' hL'
    refine ⟨sf, hst, ?_⟩
    rcases hout with ⟨hpcf, hrunf, P1, hmf, hQ'⟩ | ⟨hpan, P1, hmp, hQp'⟩ | ⟨hoom_st, hmo⟩
    · rw [← sepConj_assoc] at hmf
      exact Or.inl ⟨hpcf, hrunf, P1 ∗ F_peel, hmf, hQ sf P1 hpcf hrunf hQ'⟩
    · rw [← sepConj_assoc] at hmp
      exact Or.inr (Or.inl ⟨hpan, P1 ∗ F_peel, hmp, hQp sf P1 hpan hQp'⟩)
    · exact Or.inr (Or.inr ⟨hoom_st, hoom sf F_peel R' hoom_st hmo⟩)

/-- Panic-aware multi-cutpoint well-founded CFG fixpoint combinator with an in-context cutpoint
    transition continuation and state-aware measure `meas : Label → State → Nat`. -/
theorem SepWPp.cfg_fixpoint_wf_cps {Label : Type _} {prog : Program} {ret_pc : BitVec 64}
    (cut_pc : Label → BitVec 64)
    (meas : Label → State → Nat)
    (P_inv : Label → State → SepProp)
    (Inv : Label → State → Prop)
    (Q : Label → State → SepProp → Prop)
    (Qp : State → SepProp → Prop)
    {oom : State → SepProp}
    {l0 : Label} {s0 : State} {P : SepProp}
    (hpc0 : s0.pc = cut_pc l0)
    (hrun0 : s0.status = .Running)
    (hent0 : P ⊢ P_inv l0 s0)
    (hinv0 : Inv l0 s0)
    (hstep : ∀ (l : Label) (st : State),
      st.pc = cut_pc l → st.status = .Running → Inv l st →
      (∀ (l' : Label) (st' : State), meas l' st' < meas l st →
        st'.pc = cut_pc l' → st'.status = .Running → Inv l' st' →
        SepWPp prog ret_pc st' (P_inv l' st') (Q l') Qp oom) →
      SepWPp prog ret_pc st (P_inv l st) (Q l) Qp oom) :
    SepWPp prog ret_pc s0 P (Q l0) Qp oom := by
  intro R hm hL
  suffices h : ∀ (n : Nat) (l : Label) (st : State), meas l st = n →
      st.pc = cut_pc l → st.status = .Running → Inv l st →
      SepWPp prog ret_pc st (P_inv l st) (Q l) Qp oom from
    h (meas l0 s0) l0 s0 rfl hpc0 hrun0 hinv0 R (Satisfies.mono (sepConj_mono_left hent0) hm) hL
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro l st hn hpc hrun hinv
    refine hstep l st hpc hrun hinv ?_
    intro l' st' hlt hpc' hrun' hinv'
    exact ih (meas l' st') (hn ▸ hlt) l' st' rfl hpc' hrun' hinv'

end

end ProofLib
