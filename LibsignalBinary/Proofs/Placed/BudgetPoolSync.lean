/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import VerifiedLibraries.RustStd.Proofs.ExecSegSym
public import ProofLib.SepLogic.WPp
public meta import ProofLib.SepLogic.WP -- shake: keep
public meta import Lean -- shake: keep

/-!
# Budget Pool Transport Across Multi-Placed Instruction Segments

`SepWP.step_str*` and `SepWP.step_stp*` abstract updated memory as `∀ m' : Memory, ... (s'.setMem m')`
without exposing `m'.perm = s.mem.perm`, while `SepWP.lift_noSyscalls_vmPreserved` requires
`externAt? pc = none` everywhere. Mapping active hooks to `.Exception` via `hooksException` preserves
`fetch`, `fetchMem`, and `CodeLoaded` while ensuring every `.Running` step executes a non-`svc #0`
CPU instruction, enabling `sepWP_seg_ls_vm`, `sepWPp_seg_ls_vm`, and `wp_steps_sync_pool` to
transport `A.pool lim st` across basic blocks without unfolding `libsignalSessionLib`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.Placed.BudgetPoolSync


open _root_.Arm64 _root_.Arm64.Obj ProofLib
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalSessionLib lsmpl)
open VerifiedLibraries.RustStd (checkBlockNoSvc0 blockProgram_rebase_allInstrs_not_isSvc0)

/-- Map every active hook in `H` to an immediate `.Exception`, preserving `(externAt? pc).isSome`,
    `fetch`, `fetchMem`, and `CodeLoaded` while guaranteeing that any `.Running` reachability step
    executes a non-`svc #0` CPU instruction. -/
def hooksException (H : LibsignalHooks) : LibsignalHooks :=
  fun n => (H n).map (fun _ s => s.setStatus (.Exception "ext"))

private theorem option_or_isSome {α : Type} (o₁ o₂ : Option α) :
    (o₁.or o₂).isSome = (o₁.isSome || o₂.isSome) := by cases o₁ <;> rfl

private theorem findSome?_isSome_congr {α β γ : Type} (l : List α)
    (f : α → Option β) (g : α → Option γ) (h : ∀ x, (f x).isSome = (g x).isSome) :
    (l.findSome? f).isSome = (l.findSome? g).isSome := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.findSome?]
    cases hf : f x <;> cases hg : g x
    · exact ih
    · have hx := h x; rw [hf, hg] at hx; cases hx
    · have hx := h x; rw [hf, hg] at hx; cases hx
    · rfl

private theorem findSome?_ite_map_status {α : Type} (l : List (String × Nat)) (off : Nat)
    (tbl : String → Option α) {f : State → State}
    (h : (l.findSome? fun (n, o) =>
      if o == off then (tbl n).map (fun _ (s : State) => s.setStatus (.Exception "ext")) else none) =
      some f)
    (s : State) : (f s).status = .Exception "ext" := by
  induction l with
  | nil => simp [List.findSome?] at h
  | cons hd tl ih =>
    rcases hd with ⟨n, o⟩
    simp only [List.findSome?] at h
    cases ho : o == off
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
      exact ih h
    · simp only [ho, ↓reduceIte] at h
      cases htn : tbl n with
      | none => simp only [htn, Option.map] at h; exact ih h
      | some _ => simp only [htn, Option.map] at h; injection h with hf; subst hf; cases s; rfl

private theorem blockProgram_hooksException_externAt?_isSome (lib : MultiPlacedLib)
    (pl : MultiPlacement) (i : Nat) (H : LibsignalHooks) (pc : BitVec 64) :
    ((lib.blockProgram pl i (hooksException H)).externAt? pc).isSome =
      ((lib.blockProgram pl i H).externAt? pc).isSome := by
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program
  dsimp only
  rw [option_or_isSome, option_or_isSome]
  rw [findSome?_isSome_congr _
    (fun x : String × Nat =>
      if (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) = true then hooksException H x.1 else none)
    (fun x : String × Nat =>
      if (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) = true then H x.1 else none)]
  intro x
  cases h : (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) <;> simp [hooksException]

private theorem blockProgram_hooksException_externAt?_not_running {lib : MultiPlacedLib}
    {pl : MultiPlacement} {i : Nat} {H : LibsignalHooks} {pc : BitVec 64} {f : State → State}
    (h : (lib.blockProgram pl i (hooksException H)).externAt? pc = some f)
    (s : State) : (f s).status ≠ .Running := by
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program at h
  dsimp only [hooksException] at h
  have hnone : ∀ (l : List (String × Nat)),
      (l.findSome? fun (_ : String × Nat) => (none : Option (State → State))) = none := by
    intro l; induction l with | nil => rfl | cons _ _ ih => exact ih
  simp only [ite_self, hnone, Option.or_none] at h
  rw [findSome?_ite_map_status _ _ _ h]
  decide

private theorem blockProgram_hooks_allInstrs_eq (lib : MultiPlacedLib) (pl : MultiPlacement)
    (i : Nat) (X : String → Option (State → State)) :
    (lib.blockProgram pl i X).allInstrs (fun ins => !ins.isSvc0) =
      ((lib.blockProgram pl i).rebase (pl.base i) (fun _ => none)).allInstrs
        (fun ins => !ins.isSvc0) := by rfl

private theorem blockProgram_codeLoaded_congr {lib : MultiPlacedLib} {pl : MultiPlacement}
    {i : Nat} {X Y : String → Option (State → State)} {m : Memory}
    (h : (lib.blockProgram pl i X).CodeLoaded m) :
    (lib.blockProgram pl i Y).CodeLoaded m :=
  h.of_base_code (by rfl) (by rfl)

private theorem strip_codeLoaded_of_keep {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun k hk => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 k - prog.base = BitVec.ofNat 64 k := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 k) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hk
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq k hk, hL.perm_eq k hk, hL.isLazyFree_eq k hk⟩

private theorem strip_execOnlyIn_of_keep (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := fun _ hpx =>
  of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem steps_multi_lift_strip (lib : MultiPlacedLib) (pl : MultiPlacement) (i : Nat)
    (H : LibsignalHooks)
    (hall : (lib.blockProgram pl i (hooksException H)).allInstrs
      (fun ins => !ins.isSvc0) = true)
    {s1' sf' : State}
    (hsteps : Steps (lib.blockProgram pl i (hooksException H)) s1' sf')
    (hrun_f : sf'.status = .Running) :
    let Q := lib.blockProgram pl i (hooksException H)
    let P := lib.blockProgram pl i H
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep Q) s1 → Q.CodeLoaded s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (ProofLib.progKeep Q) sf ∧
        Steps P s1 sf ∧ ProofLib.NonSyscallPreserved s1 sf := by
  intro Q P
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, ProofLib.NonSyscallPreserved.refl s1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1
    have hrb' : sb'.status = .Running := steps_start_running hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ =>
      exact False.elim (blockProgram_hooksException_externAt?_not_running he _ hrb')
    | extern_fault _ _ _ => cases s1; cases hrb'
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := (by cases s1; exact hr1')
      have hL1' : Q.CodeLoaded (ProofLib.stripS (ProofLib.progKeep Q) s1).mem :=
        strip_codeLoaded_of_keep hL1
      have hexec' : Q.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep Q) s1).mem :=
        strip_execOnlyIn_of_keep Q s1.mem
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall hL1' hexec' _ inst hfe'
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).pc = s1.pc := (by cases s1; rfl)
        have hmem_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).mem =
            ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem := (by cases s1; rfl)
        rw [hpc_eq, hmem_eq] at hfe'
        unfold Program.fetchMem at hfe' ⊢
        have his : (Q.externAt? s1.pc).isSome = (P.externAt? s1.pc).isSome :=
          blockProgram_hooksException_externAt?_isSome lib pl i H s1.pc
        rw [his] at hfe'
        cases heP : (P.externAt? s1.pc).isSome
        · simp only [heP, Bool.false_eq_true, ↓reduceIte] at hfe' ⊢
          by_cases hal_pc : s1.pc.toNat % 4 = 0
          · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe' ⊢
            split at hfe'
            · contradiction
            · rename_i hce'
              have hce : s1.mem.canExec s1.pc 4 = true := by
                simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
                unfold Memory.canExec at hce' ⊢
                rw [Memory.allPerm_iff] at hce' ⊢
                intro k hk
                have hxk := hce' k hk
                rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
              have hr32 : (ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem).read32 s1.pc =
                  s1.mem.read32 s1.pc := by
                simp [Memory.read32, ProofLib.strip_read8]
              rw [hr32] at hfe'
              simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact hfe'
          · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'
            contradiction
        · simp only [heP, ↓reduceIte] at hfe'
          contradiction
      have hev_Q : Q.evalInst inst (ProofLib.stripS (ProofLib.progKeep Q) s1) =
          ProofLib.stripS (ProofLib.progKeep Q) (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      have hLQ_next : Q.CodeLoaded (execInst inst s1).mem := hstep_P.codeLoaded hL1
      obtain ⟨sf, hsf_eq, hsteps_P, hnsp_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_Q hLQ_next
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P,
        ProofLib.NonSyscallPreserved.trans
          (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1) hnsp_rest⟩

private theorem sepWP_seg_multi_vm {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {prog Q : Program} {blkLib : PlacedLib}
    {i : Nat} {H : LibsignalHooks}
    (hP_eq : prog = lib.blockProgram mpl i H)
    (hQ_eq : Q = lib.blockProgram mpl i (hooksException H))
    (hlib : blkLib = lib.blockLib i)
    (hchk : checkBlockNoSvc0 blkLib.text = true)
    {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : ∀ m_strip : Memory,
      SepWP Q mid (s.setMem m_strip) Pre (fun sm' Pm =>
        ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
          SepWP prog target (sm'.setMem m_real) Pm post oom)) :
    SepWP prog target s Pre post oom := by
  subst hP_eq; subst hQ_eq; subst hlib
  let Q0 := lib.blockProgram mpl i (hooksException H)
  let P0 := lib.blockProgram mpl i H
  have hall0 := blockProgram_rebase_allInstrs_not_isSvc0 lib mpl i hchk
  have hall : Q0.allInstrs (fun ins => !ins.isSvc0) = true :=
    (blockProgram_hooks_allInstrs_eq lib mpl i (hooksException H)).trans hall0
  let keep := ProofLib.progKeep Q0
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  have hL_Q0 : Q0.CodeLoaded s.mem := blockProgram_codeLoaded_congr hL
  have hL_Qstrip : Q0.CodeLoaded (ProofLib.stripExecOutside keep s.mem) :=
    strip_codeLoaded_of_keep hL_Q0
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hm
  have hseg_run := SepWP.to_reaches_pc (hseg (ProofLib.stripExecOutside keep s.mem)) hm_strip hL_Qstrip
  rcases hseg_run with ⟨sm', hstepsQ, ⟨_, hrun_m', Pm, hmm', hcont⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨sm, hsm_eq, hstepsP0, hnsp⟩ :=
      steps_multi_lift_strip lib mpl i H hall hstepsQ hrun_m' s rfl hL_Q0
    have hsm_setMem : sm'.setMem sm.mem = sm := by
      rw [hsm_eq]; cases sm; rfl
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := fun a => congrFun hnsp.2.1 a
    have hmm'_mem : ProofLib.stripExecOutside keep sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keep sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hnsp' : ProofLib.NonSyscallPreserved s (sm'.setMem sm.mem) := hsm_setMem.symm ▸ hnsp
    have hwp_cont := hcont sm.mem hnsp'
    have hmm_set : (sm'.setMem sm.mem).mem ⊨ Pm ∗ R := by rw [hsm_setMem]; exact hmm
    have hL_m : P0.CodeLoaded (sm'.setMem sm.mem).mem := by
      rw [hsm_setMem]; exact hstepsP0.codeLoaded hL
    obtain ⟨sf, hsteps2, hout2⟩ := SepWP.to_reaches_pc hwp_cont hmm_set hL_m
    rw [hsm_setMem] at hsteps2
    exact ⟨sf, hstepsP0.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem sepWPp_seg_multi_vm {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {prog Q : Program} {blkLib : PlacedLib}
    {i : Nat} {H : LibsignalHooks}
    (hP_eq : prog = lib.blockProgram mpl i H)
    (hQ_eq : Q = lib.blockProgram mpl i (hooksException H))
    (hlib : blkLib = lib.blockLib i)
    (hchk : checkBlockNoSvc0 blkLib.text = true)
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {post Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : ∀ m_strip : Memory,
      SepWP Q mid (s.setMem m_strip) Pre (fun sm' Pm =>
        ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
          SepWPp prog ret (sm'.setMem m_real) Pm post Qp oom)) :
    SepWPp prog ret s Pre post Qp oom := by
  subst hP_eq; subst hQ_eq; subst hlib
  let Q0 := lib.blockProgram mpl i (hooksException H)
  let P0 := lib.blockProgram mpl i H
  have hall0 := blockProgram_rebase_allInstrs_not_isSvc0 lib mpl i hchk
  have hall : Q0.allInstrs (fun ins => !ins.isSvc0) = true :=
    (blockProgram_hooks_allInstrs_eq lib mpl i (hooksException H)).trans hall0
  let keep := ProofLib.progKeep Q0
  intro R hm hL
  have hL_Q0 : Q0.CodeLoaded s.mem := blockProgram_codeLoaded_congr hL
  have hL_Qstrip : Q0.CodeLoaded (ProofLib.stripExecOutside keep s.mem) :=
    strip_codeLoaded_of_keep hL_Q0
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hm
  have hseg_run := SepWP.to_reaches_pc (hseg (ProofLib.stripExecOutside keep s.mem)) hm_strip hL_Qstrip
  rcases hseg_run with ⟨sm', hstepsQ, ⟨_, hrun_m', Pm, hmm', hcont⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨sm, hsm_eq, hstepsP0, hnsp⟩ :=
      steps_multi_lift_strip lib mpl i H hall hstepsQ hrun_m' s rfl hL_Q0
    have hsm_setMem : sm'.setMem sm.mem = sm := by
      rw [hsm_eq]; cases sm; rfl
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := fun a => congrFun hnsp.2.1 a
    have hmm'_mem : ProofLib.stripExecOutside keep sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keep sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hnsp' : ProofLib.NonSyscallPreserved s (sm'.setMem sm.mem) := hsm_setMem.symm ▸ hnsp
    have hwp_cont := hcont sm.mem hnsp'
    have hmm_set : (sm'.setMem sm.mem).mem ⊨ Pm ∗ R := by rw [hsm_setMem]; exact hmm
    have hL_m : P0.CodeLoaded (sm'.setMem sm.mem).mem := by
      rw [hsm_setMem]; exact hstepsP0.codeLoaded hL
    obtain ⟨sf, hsteps2, hout2⟩ := hwp_cont R hmm_set hL_m
    rw [hsm_setMem] at hsteps2
    exact ⟨sf, hstepsP0.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- Run a pure non-`svc #0` instruction segment of `lsProg_<i> H` up to `mid`, delivering
    `ProofLib.NonSyscallPreserved s (sm'.setMem m_real)` so `A.pool lim st s` transports across
    `SepWP.step_str*` / `SepWP.step_stp*` memory abstractions without unfolding `libsignalSessionLib`. -/
theorem sepWP_seg_ls_vm [LibsignalPlacement] {prog Q : Program} {blkLib : PlacedLib}
    {i : Nat} {H : LibsignalHooks}
    [hprog : IsLsBlockProg prog i H] [hQ : IsLsBlockProg Q i (hooksException H)]
    (hlib : blkLib = libsignalSessionLib.blockLib i)
    (hchk : checkBlockNoSvc0 blkLib.text = true := by rfl)
    {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : ∀ m_strip : Memory,
      SepWP Q mid (s.setMem m_strip) Pre (fun sm' Pm =>
        ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
          SepWP prog target (sm'.setMem m_real) Pm post oom)) :
    SepWP prog target s Pre post oom :=
  sepWP_seg_multi_vm hprog.eq_blockProgram hQ.eq_blockProgram hlib hchk hseg

/-- Panic-aware (`SepWPp`) counterpart of `sepWP_seg_ls_vm`. -/
theorem sepWPp_seg_ls_vm [LibsignalPlacement] {prog Q : Program} {blkLib : PlacedLib}
    {i : Nat} {H : LibsignalHooks}
    [hprog : IsLsBlockProg prog i H] [hQ : IsLsBlockProg Q i (hooksException H)]
    (hlib : blkLib = libsignalSessionLib.blockLib i)
    (hchk : checkBlockNoSvc0 blkLib.text = true := by rfl)
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {post Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : ∀ m_strip : Memory,
      SepWP Q mid (s.setMem m_strip) Pre (fun sm' Pm =>
        ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
          SepWPp prog ret (sm'.setMem m_real) Pm post Qp oom)) :
    SepWPp prog ret s Pre post Qp oom :=
  sepWPp_seg_multi_vm hprog.eq_blockProgram hQ.eq_blockProgram hlib hchk hseg


open Lean Meta Elab Tactic Arm64 ProofLib in
/-- Step CPU instructions of `lsProg_<i> H` up to `mid` (e.g. a `bl` callee entry) and transport
    `A.pool lim st s` (or `(A.atState lim st s).pool`) across `SepWP.step_str*` / `SepWP.step_stp*`
    memory abstractions in either a `SepWP` or `SepWPp` goal. -/
elab "wp_steps_sync_pool " mid:term : tactic => do
  let g ← getMainGoal
  let (isWpp, qStx, hlibStx) ← g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    let isWpp ←
      if ty.isAppOfArity ``SepWP 6 then pure false
      else if ty.isAppOfArity ``SepWPp 7 then pure true
      else throwError "wp_steps_sync_pool: expected SepWP or SepWPp goal"
    let progE ← withReducible (whnf (ty.getArg! 0))
    if !progE.isAppOfArity ``Program.rebase 4 then
      throwError "wp_steps_sync_pool: expected Program.rebase program"
    let cE := progE.getArg! 0
    let bE := progE.getArg! 1
    let xE := progE.getArg! 2
    let oE := progE.getArg! 3
    let cConst := cE.getAppFn
    if !cConst.isConst then
      throwError "wp_steps_sync_pool: expected blkPC_<idx> constant"
    let cNm := cConst.constName!
    let eqNm := cNm.getPrefix ++ Name.mkSimple (cNm.getString!.replace "blkPC_" "blkLib_eq_")
    let qE := mkApp4 (Lean.mkConst ``Program.rebase) cE bE
      (mkApp (Lean.mkConst ``LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException) xE) oE
    pure (isWpp, ← Lean.Elab.Term.exprToSyntax qE, mkIdent eqNm)
  if isWpp then
    evalTactic (← `(tactic| (
      apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWPp_seg_ls_vm (Q := $qStx) $hlibStx (mid := $mid)
      intro _m_strip
      wp_steps
      refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
      first
        | refine ProofLib.SepWPp.transport_budgetPool
            (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
            (hnext := ?_)
        | refine ProofLib.SepWPp.transport_atStatePool
            (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
            (hnext := ?_)
    )))
  else
    evalTactic (← `(tactic| (
      apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm (Q := $qStx) $hlibStx (mid := $mid)
      intro _m_strip
      wp_steps
      refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
      first
        | refine ProofLib.SepWP.transport_budgetPool
            (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
            (hnext := ?_)
        | refine ProofLib.SepWP.transport_atStatePool
            (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
            (hnext := ?_)
    )))

end LibsignalBinary.Proofs.Placed.BudgetPoolSync
