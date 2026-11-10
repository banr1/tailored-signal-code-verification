/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.Placed.Multi
public import VerifiedLibraries.Musl.Proofs.MemOps
public import VerifiedLibraries.Mallocng.Spec

/-!
# Block-Local `BlockExternFree` Pure-Words Lift & Register-Exact `blk20`/`blk21` `RunsTo` Enabler (`LibsignalBinary.Heap.MuslMemOpsRunsTo`)

- **Role:** `Role::Proof` (untrusted proof module outside the TCB; Plan W6 enabler, Card `S2P-B`).
- **Overview:**
  1. `D1-probe`: Proves repo-side block-local `steps_lift_pureWords_blockExternFree` and
     `subroutine_ok_lift_pureWords_blockExternFree` (plus `anySvc` variants for `S2P-A`) from
     public `ProofLib` / `Arm64` APIs alone (`0` `import all`, `0` engine edits), replacing
     global `∀ pc, P.externAt? pc = none` and `HooksUnfetched` with
     `BlockExternFree P addr (4 * words.length)`.
  2. Certifies via `decide +kernel` on `memcpySymWords` (`99` words = `396` B) and `memsetWordsSym`
     (`65` words = `260` B) both upper-bound write confinement and per-register minimality:
     - `blk20` (`memcpy`): exact destination set `{x1..x17, nzcv}` (preserves `x0`, `x18..x30`, `sp`, `v0..v31`).
     - `blk21` (`memset`): exact destination set `{x1..x5, v0, nzcv}` (`x6..x8` are never written in
       `memsetWordsSym`, vs the coarser `{x1..x8, v0, nzcv}` superset; preserves `x0`, `x6..x30`, `sp`, `v1..v31`).
  3. Lifts `memcpyRO_codeAt_ok_sym` and `memset_codeAt_ok_sym` through a write-tightened memory view
     `tightenMem` (`0` `import all`) and lockstep `execInst` simulation to raw-state register-exact
     `Steps P s sf` theorems with `sf = applyMemcpyClobber s (s.mem.writeBytes dst bs) (s.readReg64 .lr) c`
     and `sf = applyMemsetClobber s (s.mem.writeBytes dst (List.replicate len val)) (s.readReg64 .lr) c`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Heap.MuslMemOpsRunsTo

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (
  memcpySymWords memsetWordsSym
  memcpy_codeAt_ok_sym memcpyRO_codeAt_ok_sym memset_codeAt_ok_sym
  memcpySymSpec memcpyROSymSpec memsetSymSpec
)

/-! ## 1. Shared Block-Local Hook-Freedom Premise (`BlockExternFree`) -/

/-- No external or override hook of `P` has its entry point inside `[base, base + len)`.
    Shared premise name coordinated with `S2P-A` (`W3`/`W4`). -/
abbrev BlockExternFree (P : Program) (base : BitVec 64) (len : Nat) : Prop :=
  ∀ a : BitVec 64, ProofLib.InRegion base len a → P.externAt? a = none

/-! ## 2. Repo-Side `pureWordsProg` `CodeLoaded` & `stripS` Helpers (`0` `import all`) -/

theorem ss_mem_local (p : BitVec 64 → Bool) (s : State) :
    (stripS p s).mem = stripExecOutside p s.mem := by
  cases s; rfl

theorem ss_pc_local (p : BitVec 64 → Bool) (s : State) :
    (stripS p s).pc = s.pc := by
  cases s; rfl

theorem ss_sp_local (p : BitVec 64 → Bool) (s : State) :
    (stripS p s).sp = s.sp := by
  cases s; rfl

theorem ss_r64_local (p : BitVec 64 → Bool) (s : State) (r : Reg) :
    (stripS p s).readReg64 r = s.readReg64 r := by
  cases s; rfl

theorem strip_perm_in_code_local {prog : Program} {m : Memory} {a : BitVec 64}
    (ha : (a - prog.base).toNat < prog.code.length) :
    (stripExecOutside (progKeep prog) m).perm a = m.perm a :=
  strip_perm_of_keep (decide_eq_true ha)

theorem strip_execOnlyIn_local (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (stripExecOutside (progKeep prog) m) := by
  intro a hx
  exact of_decide_eq_true (strip_perm_x_imp hx).2

private theorem readWordOff_bounds_local {P : Program} {off : Nat} {w : BitVec 32}
    (h : P.readWordOff off = some w) : off % 4 = 0 ∧ off + 3 < P.code.length := by
  unfold Program.readWordOff at h
  by_cases hmod : off % 4 = 0
  · simp only [hmod, ne_eq, not_true_eq_false, ↓reduceIte] at h
    rcases hd : P.code.drop off with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;>
      rw [hd] at h <;> try contradiction
    have hdl : (P.code.drop off).length = P.code.length - off := List.length_drop
    rw [hd] at hdl; simp only [List.length_cons] at hdl; exact ⟨hmod, by omega⟩
  · simp only [hmod, ne_eq, not_false_eq_true, ↓reduceIte] at h; contradiction

theorem codeLoaded_pureWordsProg_of_hasWords {P : Program} {m : Memory}
    {addr : BitVec 64} {words : List (BitVec 32)}
    (hP : P.CodeLoaded m) (hw : P.hasWords addr words) (hne : words ≠ []) :
    (pureWordsProg addr words).CodeLoaded m := by
  let off := (addr - P.base).toNat
  have hpos : 0 < words.length := List.length_pos_iff.mpr hne
  have hoff_al : off % 4 = 0 := (readWordOff_bounds_local (hw.2.1 0 hpos)).1
  have hlt_end : off + 4 * (words.length - 1) + 3 < P.code.length :=
    (readWordOff_bounds_local (hw.2.1 (words.length - 1) (by omega))).2
  have hoff_end : off + 4 * words.length ≤ P.code.length := by omega
  have hbase_al := hP.aligned
  have hno_wrap := hP.no_wrap
  have haddr_nat : addr.toNat = P.base.toNat + off := by
    have : off < P.code.length := by omega
    dsimp [off] at this ⊢; bv_omega
  have hclen : (pureWordsProg addr words).code.length = 4 * words.length :=
    Program.length_flatMap_wordToBytesLE words
  refine Program.CodeLoaded.intro (by change addr.toNat % 4 = 0; omega)
    (by change addr.toNat + (pureWordsProg addr words).code.length ≤ 2 ^ 64; omega) fun k hk => ?_
  rw [hclen] at hk
  have hkP : off + k < P.code.length := by omega
  have haddr_k : (pureWordsProg addr words).base + BitVec.ofNat 64 k = P.base + BitVec.ofNat 64 (off + k) := by
    change addr + BitVec.ofNat 64 k = P.base + BitVec.ofNat 64 (off + k)
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hc_eq : P.code[off + k] = (pureWordsProg addr words).code[k]'(hclen ▸ hk) := by
    have hq := Program.code_getElem?_of_hasWordsOff hw k hk
    rw [List.getElem?_eq_getElem hkP] at hq
    change some P.code[off + k] = (pureWordsProg addr words).code[k]? at hq
    rw [List.getElem?_eq_getElem (hclen ▸ hk)] at hq; exact Option.some.inj hq
  rw [haddr_k, ← hc_eq]
  exact ⟨hP.byte_eq (off + k) hkP, hP.perm_eq (off + k) hkP, hP.isLazyFree_eq (off + k) hkP⟩

theorem strip_codeLoaded_local {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (stripExecOutside (progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hin : (prog.base + BitVec.ofNat 64 i - prog.base).toNat < prog.code.length := by
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi
  rw [strip_read8, strip_perm_in_code_local hin, strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

/-! ## 3. Block-Local `Steps` & `subroutine_ok` Lift (`BlockExternFree`, Zero `HooksUnfetched`) -/

/-- Lift a running execution `Steps (pureWordsProg addr words) s1' sf'` (`sf'.status = .Running`)
    to `Steps P s1 sf` for **any** `P : Program` (arbitrary `P.svc`, since `!i.isSvc` implies
    `i.isSvc0 = false`) and block-local `BlockExternFree P addr (4 * words.length)`, without
    `P.hasWords` or global `HooksUnfetched`. Shared helper with `S2P-A`. -/
theorem steps_lift_pureWords_anySvc_withRel_blockExternFree {P : Program}
    {addr : BitVec 64} {words : List (BitVec 32)}
    {pred : Instr → Bool} {R_inst : State → State → Prop}
    (hall : (pureWordsProg addr words).allInstrs
      (fun i => !i.isSvc && !i.isMsrTpidrEl0 && pred i) = true)
    (hext : BlockExternFree P addr (4 * words.length))
    (hR_refl : ∀ s, R_inst s s)
    (hR_trans : ∀ {s1 s2 s3}, R_inst s1 s2 → R_inst s2 s3 → R_inst s1 s3)
    (hR_step : ∀ {inst : Instr} (s : State),
      pred inst = true → s.status = .Running → (execInst inst s).status = .Running →
      R_inst s (execInst inst s))
    {s1' sf' : State} (hsteps : Steps (pureWordsProg addr words) s1' sf')
    (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = stripS (progKeep (pureWordsProg addr words)) s1 →
      (pureWordsProg addr words).CodeLoaded s1.mem →
      ∃ sf : State,
        Steps P s1 sf ∧
        sf' = stripS (progKeep (pureWordsProg addr words)) sf ∧
        ProcessFieldsPreserved s1 sf ∧
        R_inst s1 sf := by
  let prog₀ := pureWordsProg addr words
  have hclen : prog₀.code.length = 4 * words.length :=
    Program.length_flatMap_wordToBytesLE words
  induction hsteps with
  | refl _ =>
    intro s1 hs1 _
    exact ⟨s1, Steps.refl s1, hs1, ProcessFieldsPreserved.refl s1, hR_refl s1⟩
  | @step sa' sb' _ hstep hrest ih =>
    intro s1 hsa hL1
    have hL1' : prog₀.CodeLoaded sa'.mem := by
      rw [hsa, ss_mem_local]; exact strip_codeLoaded_local hL1
    cases hstep with
    | halt_unmapped _ _ _ =>
      have heq := Steps.from_not_running hrest (by simp)
      subst heq; cases hrun_f
    | extern _ hext0 _ _ | extern_fault _ hext0 _ =>
      simp [pureWordsProg, Program.ofWords, Program.externAt?, Program.hookAtOff?] at hext0
    | @exec inst hrun' hfm' =>
      have hp_i := Program.fetchMem_of_allInstrs hall hL1'
        (by rw [hsa, ss_mem_local]; exact strip_execOnlyIn_local _ _) sa'.pc inst hfm'
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp_i
      rcases hp_i with ⟨⟨hsvc, hmsr⟩, hpred⟩
      have hsvc0 : inst.isSvc0 = false := inst.isSvc0_eq_false_of_isSvc_eq_false hsvc
      have hrun1 : s1.status = .Running := by rw [hsa] at hrun'; cases s1; exact hrun'
      have hfmP : P.fetchMem s1.mem s1.pc = some inst := by
        rw [hsa, ss_pc_local, ss_mem_local] at hfm'
        unfold Program.fetchMem at hfm' ⊢
        have he0 : prog₀.externAt? s1.pc = none := rfl
        rw [he0] at hfm'
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
          split at hfm'; · contradiction
          rename_i hce'
          simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
          have hce_all := hce'
          unfold Memory.canExec at hce_all
          rw [Memory.allPerm_iff] at hce_all
          have hx0 : ((stripExecOutside (progKeep prog₀) s1.mem).perm (s1.pc + BitVec.ofNat 64 0)).x = true :=
            hce_all 0 (by decide)
          have hpc_in_prog : (s1.pc - prog₀.base).toNat < prog₀.code.length := by
            have h0 : s1.pc + BitVec.ofNat 64 0 = s1.pc := by simp
            rw [h0] at hx0
            exact strip_execOnlyIn_local prog₀ s1.mem s1.pc hx0
          have hpc_in_reg : ProofLib.InRegion addr (4 * words.length) s1.pc := by
            dsimp [ProofLib.InRegion]
            change (s1.pc - prog₀.base).toNat < 4 * words.length
            rwa [← hclen]
          rw [hext s1.pc hpc_in_reg]
          simp only [Option.isSome_none, Bool.false_eq_true, hal_pc, ne_eq, not_true_eq_false, ↓reduceIte]
          have hce : s1.mem.canExec s1.pc 4 = true := by
            unfold Memory.canExec; rw [Memory.allPerm_iff]
            intro k hk; have hxk := hce_all k hk
            rwa [strip_perm_in_code_local (strip_execOnlyIn_local prog₀ s1.mem _ hxk)] at hxk
          have hr32 : (stripExecOutside (progKeep prog₀) s1.mem).read32 s1.pc = s1.mem.read32 s1.pc := by
            simp [Memory.read32, strip_read8]
          rw [hr32] at hfm'
          simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact hfm'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfm'; contradiction
      let s2 := P.evalInst inst s1
      have hstepP : Step P s1 s2 := Step.exec hrun1 hfmP
      have hs2_eq : s2 = execInst inst s1 :=
        evalInst_eq_execInst_of_not_isSvc0 hsvc0 s1
      have hsb_eq : prog₀.evalInst inst sa' = stripS (progKeep prog₀) s2 := by
        rw [evalInst_eq_execInst_of_not_isSvc0 hsvc0, hsa, execInst_stripS hsvc0, ← hs2_eq]
      have hrun_sb' : (prog₀.evalInst inst sa').status = .Running := by
        refine Classical.byContradiction fun hnr => ?_
        have heq := Steps.from_not_running hrest hnr
        rw [heq] at hrun_f
        exact hnr hrun_f
      have hrun_s2 : (execInst inst s1).status = .Running := by
        rw [hsb_eq, hs2_eq] at hrun_sb'
        cases he : execInst inst s1
        rw [he] at hrun_sb'
        exact hrun_sb'
      have hpf12 : ProcessFieldsPreserved s1 s2 :=
        hs2_eq ▸ execInst_preserves_processFields hsvc hmsr s1
      have hR12 : R_inst s1 s2 := hs2_eq ▸ hR_step s1 hpred hrun1 hrun_s2
      obtain ⟨sf, hstepsP, hsf_eq, hpf2f, hR2f⟩ := ih hrun_f s2 hsb_eq (hstepP.codeLoaded hL1)
      exact ⟨sf, Steps.step hstepP hstepsP, hsf_eq, hpf12.trans hpf2f, hR_trans hR12 hR2f⟩

/-- Lift a running execution `Steps (pureWordsProg addr words) s1' sf'` (`sf'.status = .Running`)
    to `Steps P s1 sf` for **any** `P : Program` with `P.svc = Syscall.standard` and block-local
    `BlockExternFree P addr (4 * words.length)`, without `P.hasWords` or global `HooksUnfetched`,
    simultaneously establishing `ProcessFieldsPreserved s1 sf` and any reflexive-transitive
    instruction invariant `R_inst s1 sf`. -/
theorem steps_lift_pureWords_blockExternFree {P : Program}
    {addr : BitVec 64} {words : List (BitVec 32)}
    {pred : Instr → Bool} {R_inst : State → State → Prop}
    (hsvc_P : P.svc = Syscall.standard)
    (hall : (pureWordsProg addr words).allInstrs
      (fun i => !i.isSvc && !i.isMsrTpidrEl0 && pred i) = true)
    (hext : BlockExternFree P addr (4 * words.length))
    (hR_refl : ∀ s, R_inst s s)
    (hR_trans : ∀ {s1 s2 s3}, R_inst s1 s2 → R_inst s2 s3 → R_inst s1 s3)
    (hR_step : ∀ {inst : Instr} (s : State), pred inst = true → R_inst s (execInst inst s))
    {s1' sf' : State} (hsteps : Steps (pureWordsProg addr words) s1' sf')
    (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = stripS (progKeep (pureWordsProg addr words)) s1 →
      (pureWordsProg addr words).CodeLoaded s1.mem →
      ∃ sf : State,
        Steps P s1 sf ∧
        sf' = stripS (progKeep (pureWordsProg addr words)) sf ∧
        ProcessFieldsPreserved s1 sf ∧
        R_inst s1 sf :=
  let _ := hsvc_P
  steps_lift_pureWords_anySvc_withRel_blockExternFree hall hext hR_refl hR_trans
    (fun s hp _ _ => hR_step s hp) hsteps hrun_f

/-- `P.svc`-generic `Steps (pureWordsProg addr words)` lift under `BlockExternFree`
    (no `P.svc = Syscall.standard` hypothesis; shared helper matching `S2P-A` byte-for-byte). -/
theorem steps_lift_pureWords_anySvc_blockExternFree {P : Program}
    {addr : BitVec 64} {words : List (BitVec 32)}
    (hall : (pureWordsProg addr words).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true)
    (hext : BlockExternFree P addr (4 * words.length))
    {s1' sf' : State} (hsteps : Steps (pureWordsProg addr words) s1' sf')
    (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = stripS (progKeep (pureWordsProg addr words)) s1 →
      (pureWordsProg addr words).CodeLoaded s1.mem →
      ∃ sf : State,
        Steps P s1 sf ∧
        sf' = stripS (progKeep (pureWordsProg addr words)) sf ∧
        ProcessFieldsPreserved s1 sf := by
  intro s1 hs1 hL1
  have hall' : (pureWordsProg addr words).allInstrs
      (fun i => !i.isSvc && !i.isMsrTpidrEl0 && true) = true := by
    simpa [Bool.and_true] using hall
  obtain ⟨sf, hst, hsf, hpf, -⟩ :=
    steps_lift_pureWords_anySvc_withRel_blockExternFree (R_inst := fun _ _ => True)
      hall' hext (fun _ => trivial) (fun _ _ => trivial) (fun _ _ _ _ => trivial)
      hsteps hrun_f s1 hs1 hL1
  exact ⟨sf, hst, hsf, hpf⟩

/-- Block-local `subroutine_ok` lift for arbitrary `P.svc` (`S2P-A` shared helper). -/
theorem subroutine_ok_lift_pureWords_anySvc_blockExternFree {α : Type}
    {P : Program} {addr : BitVec 64} {words : List (BitVec 32)} {spec : Spec α}
    (h_sub : subroutine_ok (pureWordsProg addr words) addr spec)
    (h_all : (pureWordsProg addr words).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true)
    (h_cl : ∀ m : Memory, P.CodeLoaded m → (pureWordsProg addr words).CodeLoaded m)
    (h_no_ext : BlockExternFree P addr (4 * words.length))
    (h_panic : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_exit : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (h_oom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      spec.pre x (s.setMem m) = spec.pre x s := by intro _ s _; cases s; simp [State.setMem])
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; simp [State.setMem]) :
    subroutine_ok P addr
      { spec with post := fun x s0 sf => ⌜ProcessFieldsPreserved s0 sf⌝ ∗ spec.post x s0 sf } := by
  refine Arm64.subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hLP => ?_
  let prog₀ := pureWordsProg addr words
  let kp₀ := progKeep prog₀
  have hL0 : prog₀.CodeLoaded s0.mem := h_cl s0.mem hLP
  obtain ⟨R_view, hpre_strip, hunstrip⟩ := strip_frame kp₀ hpre
  let s0' := stripS kp₀ s0
  have hpre' : s0'.mem ⊨ spec.pre x s0' ∗ R_view := by
    dsimp [s0', stripS]
    rwa [h_pre_mem, State.mem_setMem]
  obtain ⟨sf', hsteps', hout', -⟩ :=
    h_sub.no_fault_before_outcome x R_view s0'
      ((ss_pc_local kp₀ s0).trans hpc)
      (by cases s0; exact hrun) hpre'
      (by cases s0; exact hsp)
      (by rw [ss_mem_local]; exact strip_codeLoaded_local hL0)
  rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · obtain ⟨sf, hstepsP, hsf_eq, hpf⟩ :=
      steps_lift_pureWords_anySvc_blockExternFree h_all h_no_ext hsteps' hret'.2.2 s0 rfl hL0
    refine Arm64.reaches_outcome_steps hstepsP (Arm64.reaches_outcome.of_outcome (Or.inl ⟨?_, ?_, ?_⟩))
    · rcases hret' with ⟨hr_pc, hr_sp, hr_st⟩
      rw [hsf_eq, ss_pc_local] at hr_pc
      rw [hsf_eq, ss_sp_local] at hr_sp
      have hrun_sf : sf.status = .Running := by rw [hsf_eq] at hr_st; cases sf; exact hr_st
      exact ⟨hr_pc.trans (ss_r64_local kp₀ s0 Reg.lr), hr_sp.trans (ss_sp_local kp₀ s0), hrun_sf⟩
    · rw [hsf_eq] at hcc'
      rcases hcc' with ⟨hsp_cc, hcs⟩
      rw [ss_sp_local] at hsp_cc
      exact ⟨hsp_cc.trans (ss_sp_local kp₀ s0), by cases s0; cases sf; exact hcs⟩
    · rw [hsf_eq] at hpost'
      dsimp [s0', stripS] at hpost'
      rw [h_post_mem, State.mem_setMem] at hpost'
      have hpost'' : sf.mem ⊨ spec.post x s0 sf ∗ R :=
        hunstrip hpf.2.2.2.2.2.2.2 hpost'
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hpf, hpost''⟩
  · rw [h_panic] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · rw [h_exit] at he; exact False.elim (not_satisfies_false_sepConj he)
  · rw [h_oom] at ho; exact False.elim (not_satisfies_false_sepConj ho)

/-- Block-local replacement for `ProofLib.subroutine_ok_lift_pureWords_process`:
    lifts `subroutine_ok (pureWordsProg addr words) addr spec` to any `P` with
    `P.svc = Syscall.standard`, `BlockExternFree P addr (4 * words.length)`, and either
    `P.hasWords addr words` or `∀ m, P.CodeLoaded m → (pureWordsProg addr words).CodeLoaded m`,
    using `ProofLib.strip_frame` (zero `import all`, zero `HooksUnfetched`). -/
theorem subroutine_ok_lift_pureWords_blockExternFree {α : Type}
    {P : Program} {addr : BitVec 64} {words : List (BitVec 32)} {spec : Spec α}
    (h_sub : subroutine_ok (pureWordsProg addr words) addr spec)
    (h_svc : P.svc = Syscall.standard)
    (h_all : (pureWordsProg addr words).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true)
    (h_cl : ∀ m : Memory, P.CodeLoaded m → (pureWordsProg addr words).CodeLoaded m)
    (h_no_ext : BlockExternFree P addr (4 * words.length))
    (h_panic : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_exit : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (h_oom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      spec.pre x (s.setMem m) = spec.pre x s := by intro _ s _; cases s; simp [State.setMem])
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; simp [State.setMem]) :
    subroutine_ok P addr
      { spec with post := fun x s0 sf => ⌜ProcessFieldsPreserved s0 sf⌝ ∗ spec.post x s0 sf } :=
  let _ := h_svc
  subroutine_ok_lift_pureWords_anySvc_blockExternFree h_sub h_all h_cl h_no_ext
    h_panic h_exit h_oom h_pre_mem h_post_mem

private theorem pureWordsProg_hasWords_of_base0_local {words : List (BitVec 32)} (addr : BitVec 64)
    (hlen : 4 * words.length ≤ 2 ^ 64)
    (h0 : ((List.range words.length).all fun i =>
      (pureWordsProg 0#64 words).readWordOff (4 * i) == words[i]?) = true) :
    (pureWordsProg addr words).hasWords addr words :=
  pureWordsProg_hasWords hlen h0

private theorem pureWordsProg_allInstrs_of_base0_local {words : List (BitVec 32)} (addr : BitVec 64)
    {f : Instr → Bool} (h0 : (pureWordsProg 0#64 words).allInstrs f = true) :
    (pureWordsProg addr words).allInstrs f = true :=
  h0

private theorem pureWordsProg_memset_hasWords_local (addr : BitVec 64) :
    (pureWordsProg addr memsetWordsSym).hasWords addr memsetWordsSym :=
  pureWordsProg_hasWords_of_base0_local addr (by decide +kernel) (by decide +kernel)

private theorem pureWordsProg_memcpy_hasWords_local (addr : BitVec 64) :
    (pureWordsProg addr memcpySymWords).hasWords addr memcpySymWords :=
  pureWordsProg_hasWords_of_base0_local addr (by decide +kernel) (by decide +kernel)

private theorem pureWordsProg_memset_allInstrs_local (addr : BitVec 64) :
    (pureWordsProg addr memsetWordsSym).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  pureWordsProg_allInstrs_of_base0_local addr (by decide +kernel)

private theorem pureWordsProg_memcpy_allInstrs_local (addr : BitVec 64) :
    (pureWordsProg addr memcpySymWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  pureWordsProg_allInstrs_of_base0_local addr (by decide +kernel)

private theorem mallocngLib_blocks_20_lt_local :
    20 < VerifiedLibraries.mallocngLib.blocks.length := by decide

private theorem mallocngLib_blocks_21_lt_local :
    21 < VerifiedLibraries.mallocngLib.blocks.length := by decide

private theorem mallocngLib_block20_checkSegment_local :
    (VerifiedLibraries.mallocngLib.blocks[20]'mallocngLib_blocks_20_lt_local).checkSegment
      0 memcpySymWords [] = true := by decide +kernel

private theorem mallocngLib_block21_checkSegment_local :
    (VerifiedLibraries.mallocngLib.blocks[21]'mallocngLib_blocks_21_lt_local).checkSegment
      0 memsetWordsSym [] = true := by decide +kernel

theorem mallocngBlock20_hasWords_memcpy_local {mmpl : Obj.MultiPlacement}
    (hpl : VerifiedLibraries.mallocngLib.Placeable mmpl) (svc : State → State := Syscall.standard) :
    (mallocngBlockProg mmpl 20 svc).hasWords (mmpl.base 20) memcpySymWords := by
  have hseg := (Obj.MultiPlacedLib.hasWords_of_checkSegment
    (X := fun _ => none) (svc := svc)
    mallocngLib_blocks_20_lt_local hpl mallocngLib_block20_checkSegment_local).1
  simpa [mallocngBlockProg, Obj.patchRelocs] using hseg

theorem mallocngBlock21_hasWords_memset_local {mmpl : Obj.MultiPlacement}
    (hpl : VerifiedLibraries.mallocngLib.Placeable mmpl) (svc : State → State := Syscall.standard) :
    (mallocngBlockProg mmpl 21 svc).hasWords (mmpl.base 21) memsetWordsSym := by
  have hseg := (Obj.MultiPlacedLib.hasWords_of_checkSegment
    (X := fun _ => none) (svc := svc)
    mallocngLib_blocks_21_lt_local hpl mallocngLib_block21_checkSegment_local).1
  simpa [mallocngBlockProg, Obj.patchRelocs] using hseg

/-- Block-local `stdMemsetSpec` on any `P` with `P.svc = Syscall.standard` and
    `BlockExternFree P (mmpl.base 21) 260` (zero `HooksUnfetched`). -/
theorem mallocngBlock21_stdMemset_ok_blockExternFree {P : Program} {mmpl : Obj.MultiPlacement}
    (hpl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hext : BlockExternFree P (mmpl.base 21) 260) :
    subroutine_ok P (mmpl.base 21) stdMemsetSpec := by
  have hcl_pure : ∀ m : Memory, P.CodeLoaded m →
      (pureWordsProg (mmpl.base 21) memsetWordsSym).CodeLoaded m :=
    fun m hm => codeLoaded_pureWordsProg_of_hasWords
      (hcl m hm) (mallocngBlock21_hasWords_memset_local hpl Syscall.standard) (by decide)
  refine subroutine_ok_refine_entails
    (subroutine_ok_lift_pureWords_blockExternFree
      (memset_codeAt_ok_sym _ (mmpl.base 21) (pureWordsProg_memset_hasWords_local (mmpl.base 21)))
      hsvc (pureWordsProg_memset_allInstrs_local (mmpl.base 21)) hcl_pure hext
      (h_pre_mem := fun _ _ _ => rfl) (h_post_mem := fun _ _ _ _ _ => rfl)) ?_
  rintro ⟨dst, b, len⟩ R s0 hpre
  simp only [stdMemsetSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, rfl, hx2, hlt⟩, hm⟩ := hpre
  have hlen : (BitVec.ofNat 64 len).toNat = len := by
    simp only [BitVec.toNat_ofNat]; omega
  refine ⟨(dst, s0.readReg32 .x1, BitVec.ofNat 64 len), ?_, fun sf => ?_⟩
  · simp only [memsetSymSpec, CType.MutSlice8, CType.Bytes, CType.U32, CType.SizeT,
      CType.scalarTy, CType.SemType.valWf, sepConj_assoc, satisfies_pure_sepConj, hlen]
    exact ⟨⟨hx0, trivial, hx2, trivial, trivial⟩, hm⟩
  · simp only [memsetSymSpec, stdMemsetSpec, CType.MutSlice8, CType.Bytes, hlen,
      pure_sepConj_pure_assoc]
    exact sepConj_mono_left (Entails.pure_mono fun h => ⟨h.2.2, h.1⟩)

/-- Block-local `stdMemcpySpec` on any `P` with `P.svc = Syscall.standard` and
    `BlockExternFree P (mmpl.base 20) 396` (zero `HooksUnfetched`). -/
theorem mallocngBlock20_stdMemcpy_ok_blockExternFree {P : Program} {mmpl : Obj.MultiPlacement}
    (hpl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hext : BlockExternFree P (mmpl.base 20) 396) :
    subroutine_ok P (mmpl.base 20) stdMemcpySpec := by
  have hcl_pure : ∀ m : Memory, P.CodeLoaded m →
      (pureWordsProg (mmpl.base 20) memcpySymWords).CodeLoaded m :=
    fun m hm => codeLoaded_pureWordsProg_of_hasWords
      (hcl m hm) (mallocngBlock20_hasWords_memcpy_local hpl Syscall.standard) (by decide)
  refine subroutine_ok_refine_entails
    (subroutine_ok_lift_pureWords_blockExternFree
      (memcpy_codeAt_ok_sym _ (mmpl.base 20) (pureWordsProg_memcpy_hasWords_local (mmpl.base 20)))
      hsvc (pureWordsProg_memcpy_allInstrs_local (mmpl.base 20)) hcl_pure hext
      (h_pre_mem := fun _ _ _ => rfl) (h_post_mem := fun _ _ _ _ _ => rfl)) ?_
  rintro ⟨dst, src, bs⟩ R s0 hpre
  simp only [stdMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
  refine ⟨(dst, src, BitVec.ofNat 64 bs.length, bs), ?_, fun sf => ?_⟩
  · simp only [memcpySymSpec, CType.MutSlice8, CType.ShrSlice8, CType.Bytes, CType.SliceLen,
      CType.SemType.valWf, sepConj_assoc, satisfies_pure_sepConj, BitVec.toNat_ofNat]
    exact ⟨⟨hx0, hx1, hx2, trivial, Nat.mod_eq_of_lt hlt⟩, hm⟩
  · simp only [memcpySymSpec, stdMemcpySpec, CType.MutSlice8, CType.ShrSlice8, CType.Bytes,
      pure_sepConj_pure_assoc]
    exact sepConj_mono_left (Entails.pure_mono fun h => ⟨h.2.2, h.1⟩)

/-- Block-local `stdMemcpyROSpec` on any `P` with `P.svc = Syscall.standard` and
    `BlockExternFree P (mmpl.base 20) 396` (zero `HooksUnfetched`). -/
theorem mallocngBlock20_stdMemcpyRO_ok_blockExternFree {P : Program} {mmpl : Obj.MultiPlacement}
    (hpl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m)
    (hext : BlockExternFree P (mmpl.base 20) 396) :
    subroutine_ok P (mmpl.base 20) stdMemcpyROSpec := by
  have hcl_pure : ∀ m : Memory, P.CodeLoaded m →
      (pureWordsProg (mmpl.base 20) memcpySymWords).CodeLoaded m :=
    fun m hm => codeLoaded_pureWordsProg_of_hasWords
      (hcl m hm) (mallocngBlock20_hasWords_memcpy_local hpl Syscall.standard) (by decide)
  refine subroutine_ok_refine_entails
    (subroutine_ok_lift_pureWords_blockExternFree
      (memcpyRO_codeAt_ok_sym _ (mmpl.base 20) (pureWordsProg_memcpy_hasWords_local (mmpl.base 20)))
      hsvc (pureWordsProg_memcpy_allInstrs_local (mmpl.base 20)) hcl_pure hext
      (h_pre_mem := fun _ _ _ => rfl) (h_post_mem := fun _ _ _ _ _ => rfl)) ?_
  rintro ⟨dst, src, bs⟩ R s0 hpre
  simp only [stdMemcpyROSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
  refine ⟨(dst, src, BitVec.ofNat 64 bs.length, bs), ?_, fun sf => ?_⟩
  · simp only [memcpyROSymSpec, CType.MutSlice8, CType.Bytes, CType.SliceLen,
      CType.SemType.valWf, sepConj_assoc, satisfies_pure_sepConj, BitVec.toNat_ofNat]
    exact ⟨⟨hx0, hx1, hx2, trivial, Nat.mod_eq_of_lt hlt⟩, hm⟩
  · simp only [memcpyROSymSpec, stdMemcpyROSpec, CType.MutSlice8, CType.Bytes,
      pure_sepConj_pure_assoc]
    exact sepConj_mono_left (Entails.pure_mono fun h => ⟨h.2.2, h.1⟩)

/-! ## 4. Kernel-Checked Exact Destination Sets & Minimality (`memcpySymWords` / `memsetWordsSym`) -/

/-- Register read check excluding `.sp` (so `s_tight` with `sp := 0#64` agrees with `s` on every
    register read and every `checkRegSPAligned` / `checkAddrSPAligned`). -/
def regReadNoSp : Reg → Bool
  | .sp => false
  | _ => true

/-- Register destination confinement check: `.sp` is never written; `.xzr` and `.gpr 31#5` are
    no-ops; any other `.gpr idx` must satisfy `gprOk idx = true`. -/
def regWriteOk (gprOk : BitVec 5 → Bool) : Reg → Bool
  | .gpr idx => idx == 31#5 || gprOk idx
  | .xzr => true
  | .sp => false

/-- Addressing-mode confinement check: no `.sp` base/index reads, and pre/post-index writebacks
    stay within `gprOk`. -/
def addrOk (gprOk : BitVec 5 → Bool) : AddrMode → Bool
  | .Offset b _ | .UnscaledOffset b _ => regReadNoSp b
  | .PreIndex b _ | .PostIndex b _ => regReadNoSp b && regWriteOk gprOk b
  | .RegOffset b idx _ _ => regReadNoSp b && regReadNoSp idx

/-- Syntactic instruction subset covering all instructions in `memcpySymWords` and `memsetWordsSym`
    while confining GPR writes to `gprOk`, SIMD writes to `vregOk`, preserving `sp`, `fpsr`,
    `tpidrEl0`, `oracle`, `exclFails`, `trace`, and performing memory accesses solely via
    `canRead`/`readSized` and `canWrite`/`writeSized`/`writeSimdSized`/`simdStoreRegs`. -/
def instrAllowed (gprOk vregOk : BitVec 5 → Bool) : Instr → Bool
  | .adr _ rd _ | .moveWide _ _ rd _ _ => regWriteOk gprOk rd
  | .addSubImm _ _ rd rn _ _ | .logicalImm _ _ rd rn _ | .bitfield _ _ rd rn _ _
  | .dataProc1 _ _ rd rn => regReadNoSp rn && regWriteOk gprOk rd
  | .addSubShift _ _ rd rn rm _ _ | .addSubExt _ _ rd rn rm _ _
  | .logicalShift _ _ rd rn rm _ _ | .condSelect _ _ rd rn rm _
  | .extr _ rd rn rm _ | .dataProc2 _ _ rd rn rm =>
    regReadNoSp rn && regReadNoSp rm && regWriteOk gprOk rd
  | .condCompareReg _ _ rn rm _ _ => regReadNoSp rn && regReadNoSp rm
  | .condCompareImm _ _ rn _ _ _ => regReadNoSp rn
  | .b _ | .bCond _ _ | .nop => true
  | .br rn | .ret rn | .cbz _ _ rn _ | .tbz _ _ rn _ _ | .dcZva rn => regReadNoSp rn
  | .sysReg true sysreg rt => if sysreg == 0x5807#15 then regWriteOk gprOk rt else false
  | .ldr _ _ _ rt addr => addrOk gprOk addr && regWriteOk gprOk rt
  | .ldp _ _ rt1 rt2 addr => addrOk gprOk addr && regWriteOk gprOk rt1 && regWriteOk gprOk rt2
  | .str _ rt addr => addrOk gprOk addr && regReadNoSp rt
  | .stp _ rt1 rt2 addr => addrOk gprOk addr && regReadNoSp rt1 && regReadNoSp rt2
  | .strSimd _ _ addr | .stpSimd _ _ _ addr => addrOk gprOk addr
  | .simdInsDup _ op _ imm4 rn rd =>
    if !op && imm4 == 0b0001#4 then regReadNoSp (Reg.fromZRBits rn) && vregOk rd
    else if !op && imm4 == 0b0000#4 then vregOk rd
    else if !op && imm4 == 0b0111#4 then regWriteOk gprOk (Reg.fromZRBits rd)
    else false
  | _ => false

/-- Exact GPR destination set of `blk20` (`memcpySymWords`): `{x1 .. x17}`. -/
def memcpyGprOk (idx : BitVec 5) : Bool :=
  decide (1 ≤ idx.toNat ∧ idx.toNat ≤ 17)

/-- Exact GPR destination set of `blk21` (`memsetWordsSym`): `{x1 .. x5}`
    (`x6 .. x8` are never written in `memsetWordsSym`). -/
def memsetGprOk (idx : BitVec 5) : Bool :=
  decide (1 ≤ idx.toNat ∧ idx.toNat ≤ 5)

/-- Exact SIMD destination set of `blk21` (`memsetWordsSym`): `{v0}`. -/
def memsetVRegOk (idx : BitVec 5) : Bool :=
  idx == 0#5

/-- Kernel-checked upper bound for `blk20` (`memcpySymWords`): only `{x1..x17, nzcv}` can be written. -/
theorem memcpySymWords_allInstrs_allowed_base0 :
    (pureWordsProg 0#64 memcpySymWords).allInstrs
      (fun i => !i.isSvc && !i.isMsrTpidrEl0 && instrAllowed memcpyGprOk (fun _ => false) i) = true := by
  decide +kernel

theorem memcpySymWords_allInstrs_allowed (addr : BitVec 64) :
    (pureWordsProg addr memcpySymWords).allInstrs
      (fun i => !i.isSvc && !i.isMsrTpidrEl0 && instrAllowed memcpyGprOk (fun _ => false) i) = true :=
  pureWordsProg_allInstrs_of_base0_local addr memcpySymWords_allInstrs_allowed_base0

/-- Kernel-checked upper bound for `blk21` (`memsetWordsSym`): only exact `{x1..x5, v0, nzcv}` can be written. -/
theorem memsetWordsSym_allInstrs_allowed_base0 :
    (pureWordsProg 0#64 memsetWordsSym).allInstrs
      (fun i => !i.isSvc && !i.isMsrTpidrEl0 && instrAllowed memsetGprOk memsetVRegOk i) = true := by
  decide +kernel

theorem memsetWordsSym_allInstrs_allowed (addr : BitVec 64) :
    (pureWordsProg addr memsetWordsSym).allInstrs
      (fun i => !i.isSvc && !i.isMsrTpidrEl0 && instrAllowed memsetGprOk memsetVRegOk i) = true :=
  pureWordsProg_allInstrs_of_base0_local addr memsetWordsSym_allInstrs_allowed_base0

/-- Syntactic witness that a decoded instruction in `prog` satisfies `f` (`!prog.allInstrs (!f ·)`). -/
def progAnyInstr (prog : Program) (f : Instr → Bool) : Bool :=
  !prog.allInstrs (fun i => !f i)

def regIsGpr (idx : BitVec 5) : Reg → Bool
  | .gpr b => b != 31#5 && b == idx
  | _ => false

def addrWritesGpr (idx : BitVec 5) : AddrMode → Bool
  | .PreIndex b _ | .PostIndex b _ => regIsGpr idx b
  | _ => false

/-- Syntactic check that `Instr` has destination register `.gpr idx`. -/
def instrWritesGpr (idx : BitVec 5) : Instr → Bool
  | .adr _ rd _ | .moveWide _ _ rd _ _ | .addSubImm _ _ rd _ _ _
  | .logicalImm _ _ rd _ _ | .bitfield _ _ rd _ _ _ | .dataProc1 _ _ rd _
  | .addSubShift _ _ rd _ _ _ _ | .addSubExt _ _ rd _ _ _ _
  | .logicalShift _ _ rd _ _ _ _ | .condSelect _ _ rd _ _ _
  | .extr _ rd _ _ _ | .dataProc2 _ _ rd _ _ | .sysReg true _ rd => regIsGpr idx rd
  | .ldr _ _ _ rt addr => addrWritesGpr idx addr || regIsGpr idx rt
  | .ldp _ _ rt1 rt2 addr => addrWritesGpr idx addr || regIsGpr idx rt1 || regIsGpr idx rt2
  | .str _ _ addr | .stp _ _ _ addr | .strSimd _ _ addr | .stpSimd _ _ _ addr =>
    addrWritesGpr idx addr
  | .simdInsDup _ op _ imm4 _ rd =>
    !op && imm4 == 0b0111#4 && regIsGpr idx (Reg.fromZRBits rd)
  | _ => false

/-- Syntactic check that `Instr` writes SIMD register `idx`. -/
def instrWritesVReg (idx : BitVec 5) : Instr → Bool
  | .simdInsDup _ op _ imm4 _ rd =>
    (!op && imm4 == 0b0001#4 && rd == idx) || (!op && imm4 == 0b0000#4 && rd == idx)
  | _ => false

/-- Syntactic check that `Instr` writes processor flags `NZCV`. -/
def instrWritesNzcv : Instr → Bool
  | .addSubImm _ (.ADDS) _ _ _ _ | .addSubImm _ (.SUBS) _ _ _ _
  | .addSubShift _ (.ADDS) _ _ _ _ _ | .addSubShift _ (.SUBS) _ _ _ _ _
  | .addSubExt _ (.ADDS) _ _ _ _ _ | .addSubExt _ (.SUBS) _ _ _ _ _
  | .logicalImm _ (.ANDS) _ _ _ | .logicalShift _ (.ANDS) _ _ _ _ _
  | .logicalShift _ (.BICS) _ _ _ _ _
  | .condCompareReg _ _ _ _ _ _ | .condCompareImm _ _ _ _ _ _ => true
  | _ => false

/-- Minimality certificate for `blk20` (`memcpySymWords`): every GPR in `x1..x17` and `nzcv` is
    syntactically written by at least one decoded instruction in `memcpySymWords`. -/
theorem memcpySymWords_minimal_writes :
    (((List.range 17).all fun k =>
      progAnyInstr (pureWordsProg 0#64 memcpySymWords)
        (instrWritesGpr (BitVec.ofNat 5 (k + 1)))) &&
     progAnyInstr (pureWordsProg 0#64 memcpySymWords) instrWritesNzcv) = true := by
  decide +kernel

/-- Minimality certificate for `blk21` (`memsetWordsSym`): every GPR in `x1..x5`, `v0`, and `nzcv`
    is syntactically written by at least one decoded instruction in `memsetWordsSym`, whereas
    `x6`, `x7`, `x8` (the extra registers in the coarser `{x1..x8, v0, nzcv}` superset) are NEVER
    written. -/
theorem memsetWordsSym_minimal_writes :
    (((List.range 5).all fun k =>
      progAnyInstr (pureWordsProg 0#64 memsetWordsSym)
        (instrWritesGpr (BitVec.ofNat 5 (k + 1)))) &&
     progAnyInstr (pureWordsProg 0#64 memsetWordsSym) (instrWritesVReg 0#5) &&
     progAnyInstr (pureWordsProg 0#64 memsetWordsSym) instrWritesNzcv &&
     ((List.range 3).all fun k =>
      !progAnyInstr (pureWordsProg 0#64 memsetWordsSym)
        (instrWritesGpr (BitVec.ofNat 5 (k + 6))))) = true := by
  decide +kernel

/-! ## 5. Exact Clobber Witnesses (`MemcpyClobber`, `MemsetClobber`) & State Update Combinators -/

/-- Exact clobber witness for `blk20` (`memcpy`): `{x1..x17, pstate}` (`nzcv`). -/
structure MemcpyClobber where
  x1 : BitVec 64
  x2 : BitVec 64
  x3 : BitVec 64
  x4 : BitVec 64
  x5 : BitVec 64
  x6 : BitVec 64
  x7 : BitVec 64
  x8 : BitVec 64
  x9 : BitVec 64
  x10 : BitVec 64
  x11 : BitVec 64
  x12 : BitVec 64
  x13 : BitVec 64
  x14 : BitVec 64
  x15 : BitVec 64
  x16 : BitVec 64
  x17 : BitVec 64
  pstate : PState

/-- Apply the exact `blk20` (`memcpy`) post-state transition: updates `{x1..x17, pstate}`, `mem`,
    and `pc`, leaving `x0`, `x18..x30`, `sp`, `v0..v31`, and all process/system fields untouched. -/
@[reducible] def applyMemcpyClobber (s : State) (m' : Memory) (pc' : BitVec 64)
    (c : MemcpyClobber) : State :=
  ((((((((((((((((((s.writeReg64 .x1 c.x1).writeReg64 .x2 c.x2).writeReg64 .x3 c.x3).writeReg64
    .x4 c.x4).writeReg64 .x5 c.x5).writeReg64 .x6 c.x6).writeReg64 .x7 c.x7).writeReg64
    .x8 c.x8).writeReg64 .x9 c.x9).writeReg64 .x10 c.x10).writeReg64 .x11 c.x11).writeReg64
    .x12 c.x12).writeReg64 .x13 c.x13).writeReg64 .x14 c.x14).writeReg64 .x15 c.x15).writeReg64
    .x16 c.x16).writeReg64 .x17 c.x17).setPState c.pstate).setMem m' |>.setPC pc'

/-- Extract the `MemcpyClobber` values of a post-state `sf`. -/
def MemcpyClobber.ofState (sf : State) : MemcpyClobber where
  x1 := sf.regs.regs 1#5
  x2 := sf.regs.regs 2#5
  x3 := sf.regs.regs 3#5
  x4 := sf.regs.regs 4#5
  x5 := sf.regs.regs 5#5
  x6 := sf.regs.regs 6#5
  x7 := sf.regs.regs 7#5
  x8 := sf.regs.regs 8#5
  x9 := sf.regs.regs 9#5
  x10 := sf.regs.regs 10#5
  x11 := sf.regs.regs 11#5
  x12 := sf.regs.regs 12#5
  x13 := sf.regs.regs 13#5
  x14 := sf.regs.regs 14#5
  x15 := sf.regs.regs 15#5
  x16 := sf.regs.regs 16#5
  x17 := sf.regs.regs 17#5
  pstate := sf.pstate

/-- Exact clobber witness for `blk21` (`memset`): exact destination set `{x1..x5, v0, pstate}`
    (`x6..x8` are preserved, NOT clobbered; contrast with the coarser `{x1..x8, v0, nzcv}` superset). -/
structure MemsetClobber where
  x1 : BitVec 64
  x2 : BitVec 64
  x3 : BitVec 64
  x4 : BitVec 64
  x5 : BitVec 64
  v0 : BitVec 128
  pstate : PState

/-- Apply the exact `blk21` (`memset`) post-state transition: updates `{x1..x5, v0, pstate}`,
    `mem`, and `pc`, leaving `x0`, `x6..x30`, `sp`, `v1..v31`, and all process/system fields untouched. -/
@[reducible] def applyMemsetClobber (s : State) (m' : Memory) (pc' : BitVec 64)
    (c : MemsetClobber) : State :=
  ((((((((s.writeReg64 .x1 c.x1).writeReg64 .x2 c.x2).writeReg64 .x3 c.x3).writeReg64
    .x4 c.x4).writeReg64 .x5 c.x5).writeVReg128 0#5 c.v0).setPState c.pstate).setMem m').setPC pc'

/-- Extract the `MemsetClobber` values of a post-state `sf`. -/
def MemsetClobber.ofState (sf : State) : MemsetClobber where
  x1 := sf.regs.regs 1#5
  x2 := sf.regs.regs 2#5
  x3 := sf.regs.regs 3#5
  x4 := sf.regs.regs 4#5
  x5 := sf.regs.regs 5#5
  v0 := sf.vregs.regs 0#5
  pstate := sf.pstate

/-! ## 6. Write-Tightened Memory View (`tightenMem`) & Lockstep `execInst` Simulation (`0` `import all`) -/

/-- Write-tightened memory view over footprint `fp`:
    - inside `fp` (`fp a = true`): preserves permission/bytes/`lazyFree` and sets `anon := true`
      so separation-logic `Satisfies.of_perm_mono` applies even on non-anonymous `.data`/`.bss` buffers;
    - outside `fp` (`fp a = false`): strips write permission (`w := false`) on deterministically
      readable cells (`p.r && !p.lazyFree`) and hides non-readable/`lazyFree` cells (`none`). -/
def tightenMem (fp : BitVec 64 → Bool) (m : Memory) : Memory :=
  ⟨fun a =>
    if fp a then
      match m.cells a with
      | some (some p, b) => some (some { p with anon := true }, b)
      | c => c
    else
      match m.cells a with
      | some (some p, b) =>
        if p.r && !p.lazyFree then
          some (some { r := true, w := false, x := p.x, lazyFree := false, anon := true }, b)
        else none
      | _ => none⟩

private theorem tightenMem_perm_in {fp : BitVec 64 → Bool} {m : Memory} {a : BitVec 64}
    (hfp : fp a = true) : (tightenMem fp m).perm a = m.perm a := by
  dsimp only [tightenMem, Memory.perm, Perm.rwx]
  simp only [hfp, ↓reduceIte]
  rcases m.cells a with _ | ⟨_ | p, b⟩ <;> rfl

private theorem tightenMem_read8_in {fp : BitVec 64 → Bool} {m : Memory} {a : BitVec 64}
    (hfp : fp a = true) : (tightenMem fp m).read8 a = m.read8 a := by
  dsimp only [tightenMem, Memory.read8]
  simp only [hfp, ↓reduceIte]
  rcases m.cells a with _ | ⟨_ | p, b⟩ <;> rfl

private theorem tightenMem_isLazyFree_eq_false {fp : BitVec 64 → Bool} {m : Memory}
    (hlf_fp : ∀ a, fp a = true → m.isLazyFree a = false) (a : BitVec 64) :
    (tightenMem fp m).isLazyFree a = false := by
  dsimp only [tightenMem, Memory.isLazyFree]
  by_cases hfp : fp a = true
  · simp only [hfp, ↓reduceIte]
    have h := hlf_fp a hfp
    dsimp only [Memory.isLazyFree] at h
    rcases hc : m.cells a with _ | ⟨_ | p, b⟩
    · rfl
    · rfl
    · rw [hc] at h; exact h
  · simp only [hfp, Bool.false_eq_true, ↓reduceIte]
    rcases m.cells a with _ | ⟨_ | p, b⟩
    · rfl
    · rfl
    · dsimp only
      by_cases hr : (p.r && !p.lazyFree) = true
      · simp only [hr, ↓reduceIte]
      · simp only [hr, Bool.false_eq_true, ↓reduceIte]

private theorem tightenMem_isAnon_of_mapped {fp : BitVec 64 → Bool} {m : Memory} {a : BitVec 64}
    (hm : ((tightenMem fp m).perm a).mapped = true) :
    (tightenMem fp m).isAnon a = true := by
  dsimp only [tightenMem, Memory.perm, Memory.isAnon, Option.mapped] at hm ⊢
  by_cases hfp : fp a = true
  · simp only [hfp, ↓reduceIte] at hm ⊢
    rcases hc : m.cells a with _ | ⟨_ | p, b⟩
    · rw [hc] at hm; cases hm
    · rw [hc] at hm; cases hm
    · rfl
  · simp only [hfp, Bool.false_eq_true, ↓reduceIte] at hm ⊢
    rcases hc : m.cells a with _ | ⟨_ | p, b⟩
    · rw [hc] at hm; cases hm
    · rw [hc] at hm; cases hm
    · rw [hc] at hm; dsimp only at hm ⊢
      by_cases hr : (p.r && !p.lazyFree) = true
      · simp only [hr, ↓reduceIte]
      · simp only [hr, Bool.false_eq_true, ↓reduceIte, Option.isSome_none] at hm

private theorem tightenMem_canRead_imp {fp : BitVec 64 → Bool} {m : Memory} {ea : BitVec 64} {n : Nat}
    (hcr : (tightenMem fp m).canRead ea n = true) :
    m.canRead ea n = true ∧
      ∀ k < n, (tightenMem fp m).read8 (ea + BitVec.ofNat 64 k) = m.read8 (ea + BitVec.ofNat 64 k) := by
  simp only [Memory.canRead, Bool.and_eq_true, Memory.allPerm_iff, Memory.allNoLazyFree_iff] at hcr ⊢
  rcases hcr with ⟨hr_all, hlf_all⟩
  refine ⟨⟨fun k hk => ?_, fun k hk => ?_⟩, fun k hk => ?_⟩
  · have hrk := hr_all k hk
    dsimp only [tightenMem, Memory.perm, Perm.rwx, Option.r] at hrk ⊢
    by_cases hfp : fp (ea + BitVec.ofNat 64 k) = true
    · simp only [hfp, ↓reduceIte] at hrk
      rcases hc : m.cells (ea + BitVec.ofNat 64 k) with _ | ⟨_ | p, b⟩
      · rw [hc] at hrk; cases hrk
      · rw [hc] at hrk; cases hrk
      · rw [hc] at hrk; exact hrk
    · simp only [hfp, Bool.false_eq_true, ↓reduceIte] at hrk
      rcases hc : m.cells (ea + BitVec.ofNat 64 k) with _ | ⟨_ | p, b⟩
      · rw [hc] at hrk; cases hrk
      · rw [hc] at hrk; cases hrk
      · rw [hc] at hrk; dsimp only [Option.r] at hrk ⊢
        by_cases hok : (p.r && !p.lazyFree) = true
        · simp only [Bool.and_eq_true] at hok; exact hok.1
        · simp only [hok, Bool.false_eq_true, ↓reduceIte, Option.r] at hrk
  · have hrk := hr_all k hk
    have hlfk := hlf_all k hk
    dsimp only [tightenMem, Memory.perm, Memory.isLazyFree, Perm.rwx, Option.r] at hrk hlfk ⊢
    by_cases hfp : fp (ea + BitVec.ofNat 64 k) = true
    · simp only [hfp, ↓reduceIte] at hlfk
      rcases hc : m.cells (ea + BitVec.ofNat 64 k) with _ | ⟨_ | p, b⟩
      · rfl
      · rfl
      · rw [hc] at hlfk; exact hlfk
    · simp only [hfp, Bool.false_eq_true, ↓reduceIte] at hrk
      rcases hc : m.cells (ea + BitVec.ofNat 64 k) with _ | ⟨_ | p, b⟩
      · rfl
      · rfl
      · rw [hc] at hrk; dsimp only [Option.r] at hrk ⊢
        by_cases hok : (p.r && !p.lazyFree) = true
        · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok; exact hok.2
        · simp only [hok, Bool.false_eq_true, ↓reduceIte, Option.r] at hrk
  · have hrk := hr_all k hk
    dsimp only [tightenMem, Memory.perm, Memory.read8, Perm.rwx, Option.r] at hrk ⊢
    by_cases hfp : fp (ea + BitVec.ofNat 64 k) = true
    · simp only [hfp, ↓reduceIte]
      rcases m.cells (ea + BitVec.ofNat 64 k) with _ | ⟨_ | p, b⟩ <;> rfl
    · simp only [hfp, Bool.false_eq_true, ↓reduceIte] at hrk ⊢
      rcases hc : m.cells (ea + BitVec.ofNat 64 k) with _ | ⟨_ | p, b⟩
      · rfl
      · rw [hc] at hrk; cases hrk
      · rw [hc] at hrk; dsimp only [Option.r] at hrk ⊢
        by_cases hok : (p.r && !p.lazyFree) = true
        · simp only [hok, ↓reduceIte]
        · simp only [hok, Bool.false_eq_true, ↓reduceIte, Option.r] at hrk

private theorem tightenMem_readSized_eq {fp : BitVec 64 → Bool} {m : Memory}
    {sz : MemWidth} {sgn : Bool} {ea : BitVec 64}
    (hcr : (tightenMem fp m).canRead ea sz.bytes = true) :
    (tightenMem fp m).readSized sz sgn ea = m.readSized sz sgn ea := by
  have hb := (tightenMem_canRead_imp hcr).2
  cases sz with
  | B8 =>
    have h0 := hb 0 (by decide)
    have hzero : ea + BitVec.ofNat 64 0 = ea := by simp
    rw [hzero] at h0
    simp only [Memory.readSized, h0]
  | H16 =>
    have h0 := hb 0 (by decide); change (tightenMem fp m).read8 (ea + 0#64) = m.read8 (ea + 0#64) at h0
    have h1 := hb 1 (by decide); change (tightenMem fp m).read8 (ea + 1#64) = m.read8 (ea + 1#64) at h1
    simp only [Memory.readSized, Memory.read16, h0, h1]
  | W32 =>
    have h0 := hb 0 (by decide); change (tightenMem fp m).read8 (ea + 0#64) = m.read8 (ea + 0#64) at h0
    have h1 := hb 1 (by decide); change (tightenMem fp m).read8 (ea + 1#64) = m.read8 (ea + 1#64) at h1
    have h2 := hb 2 (by decide); change (tightenMem fp m).read8 (ea + 2#64) = m.read8 (ea + 2#64) at h2
    have h3 := hb 3 (by decide); change (tightenMem fp m).read8 (ea + 3#64) = m.read8 (ea + 3#64) at h3
    simp only [Memory.readSized, Memory.read32, h0, h1, h2, h3]
  | X64 =>
    have h0 := hb 0 (by decide); change (tightenMem fp m).read8 (ea + 0#64) = m.read8 (ea + 0#64) at h0
    have h1 := hb 1 (by decide); change (tightenMem fp m).read8 (ea + 1#64) = m.read8 (ea + 1#64) at h1
    have h2 := hb 2 (by decide); change (tightenMem fp m).read8 (ea + 2#64) = m.read8 (ea + 2#64) at h2
    have h3 := hb 3 (by decide); change (tightenMem fp m).read8 (ea + 3#64) = m.read8 (ea + 3#64) at h3
    have h4 := hb 4 (by decide); change (tightenMem fp m).read8 (ea + 4#64) = m.read8 (ea + 4#64) at h4
    have h5 := hb 5 (by decide); change (tightenMem fp m).read8 (ea + 5#64) = m.read8 (ea + 5#64) at h5
    have h6 := hb 6 (by decide); change (tightenMem fp m).read8 (ea + 6#64) = m.read8 (ea + 6#64) at h6
    have h7 := hb 7 (by decide); change (tightenMem fp m).read8 (ea + 7#64) = m.read8 (ea + 7#64) at h7
    simp only [Memory.readSized, Memory.read64, h0, h1, h2, h3, h4, h5, h6, h7]

private theorem tightenMem_canWrite_imp {fp : BitVec 64 → Bool} {m : Memory} {ea : BitVec 64} {n : Nat}
    (hcw : (tightenMem fp m).canWrite ea n = true) :
    m.canWrite ea n = true ∧ ∀ k < n, fp (ea + BitVec.ofNat 64 k) = true := by
  unfold Memory.canWrite at hcw ⊢
  rw [Memory.allPerm_iff] at hcw ⊢
  have hfp_all : ∀ k < n, fp (ea + BitVec.ofNat 64 k) = true := by
    intro k hk
    have hk_w := hcw k hk
    by_cases hfp : fp (ea + BitVec.ofNat 64 k) = true
    · exact hfp
    · exfalso
      dsimp only [tightenMem, Memory.perm, Perm.rwx, Option.w] at hk_w
      simp only [hfp, Bool.false_eq_true, ↓reduceIte] at hk_w
      rcases hc : m.cells (ea + BitVec.ofNat 64 k) with _ | ⟨_ | p, b⟩ <;> rw [hc] at hk_w
      · cases hk_w
      · cases hk_w
      · dsimp only at hk_w
        by_cases hok : (p.r && !p.lazyFree) = true
        · simp only [hok, ↓reduceIte] at hk_w; cases hk_w
        · simp only [hok, Bool.false_eq_true, ↓reduceIte, Option.w, Bool.false_and] at hk_w
  refine ⟨fun k hk => ?_, hfp_all⟩
  have hk_w := hcw k hk
  rwa [tightenMem_perm_in (hfp_all k hk)] at hk_w

private theorem tightenMem_codeLoaded {prog : Program} {fp : BitVec 64 → Bool} {m : Memory}
    (hL : prog.CodeLoaded m) : prog.CodeLoaded (tightenMem fp m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  let a := prog.base + BitVec.ofNat 64 i
  have hb := hL.byte_eq i hi
  have hp := hL.perm_eq i hi
  have hlf := hL.isLazyFree_eq i hi
  change m.read8 a = prog.code[i] at hb
  change m.perm a = some Perm.rx at hp
  change m.isLazyFree a = false at hlf
  dsimp only [tightenMem, Memory.read8, Memory.perm, Memory.isLazyFree, Perm.rwx, Perm.rx] at hb hp hlf ⊢
  rcases hc : m.cells a with _ | ⟨_ | p, byte⟩ <;> rw [hc] at hb hp hlf
  · cases hp
  · cases hp
  · cases p
    simp only [Option.some.injEq, Perm.mk.injEq] at hp hlf hb
    rcases hp with ⟨hr, hw, hx, -, -⟩
    subst hr hw hx hlf hb
    by_cases hfp : fp a = true
    · simp [hfp]
    · have hfpf : fp a = false := Bool.eq_false_iff.mpr hfp
      simp [hfpf]

/-- Construct `tightenMem fp m ⊨ memRegion dst len` from `m.RW dst len` using public `ProofLib`
    theorems (`Satisfies.mapZero`, `IsBlock.memRegion`, `Satisfies.of_perm_mono`; `0` `import all`). -/
theorem satisfies_memRegion_tight {m : Memory} {dst : BitVec 64} {len : Nat}
    (hrw : m.RW dst len) :
    let fp := fun a => decide (InRegion dst len a)
    tightenMem fp m ⊨ memRegion dst len := by
  intro fp
  let m' := tightenMem fp m
  let m_unm : Memory := ⟨fun a => some (none, m'.read8 a)⟩
  have hcanMap : m_unm.canMap dst len = true := by
    rw [Memory.canMap, Memory.allPerm_iff]
    intro _ _; rfl
  have hm0 : m_unm.mapZero dst len ⊨ memRegion dst len ∗ emp :=
    Satisfies.mapZero (satisfies_emp m_unm) hcanMap
  let m1 : Memory :=
    ⟨fun a => if (a - dst).toNat < len then some (some Perm.rw, m'.read8 a) else some (none, m'.read8 a)⟩
  have hag : AgreesOutside (m_unm.mapZero dst len) m1 dst len := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a hout
      have hnot : ¬ (a - dst).toNat < len := Nat.not_lt.mpr hout
      dsimp only [m1, m_unm, Memory.mapZero, Memory.read8, Memory.perm, Option.mapped]
      simp only [hnot, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · funext a
      dsimp only [m1, m_unm, Memory.mapZero, Memory.perm, Option.mapped, Perm.rwx, Perm.rw]
      by_cases h : (a - dst).toNat < len
      · simp only [h, decide_true, ↓reduceIte]; rfl
      · simp only [h, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · intro a _
      dsimp only [m1, m_unm, Memory.mapZero, Memory.isLazyFree, Memory.perm, Option.mapped, Perm.rw]
      by_cases h : (a - dst).toNat < len
      · simp only [h, decide_true, ↓reduceIte]; rfl
      · simp only [h, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · intro a _
      dsimp only [m1, Memory.isLazyFree, Perm.rw]
      by_cases h : (a - dst).toNat < len <;> simp only [h, ↓reduceIte]
    · intro a han
      dsimp only [m1, m_unm, Memory.mapZero, Memory.isAnon, Memory.perm, Option.mapped, Perm.rw] at han ⊢
      by_cases h : (a - dst).toNat < len
      · simp only [h, ↓reduceIte]
      · simp only [h, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at han
  have hm1_emp : m1 ⊨ memRegion dst len ∗ emp :=
    (IsBlock.memRegion dst len).update (IsBlock.memRegion dst len) (Nat.le_refl _) hm0 hag trivial
  have hm1 : m1 ⊨ memRegion dst len := by rwa [sepConj_emp] at hm1_emp
  have hlf_m' : ∀ a, m'.isLazyFree a = false := by
    refine tightenMem_isLazyFree_eq_false (fun a hfp => ?_)
    have hin : InRegion dst len a := of_decide_eq_true hfp
    exact (Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hin)).2
  have hm1_read : ∀ a, m'.read8 a = m1.read8 a := by
    intro a; dsimp only [m1, Memory.read8]
    by_cases h : (a - dst).toNat < len <;> simp only [h, ↓reduceIte]
  refine Arm64.Satisfies.of_perm_mono hm1_read ?_ ?_ ?_ ?_ (fun a _ => hlf_m' a) ?_ hm1
  · intro a hp
    dsimp only [m1, Memory.perm] at hp
    by_cases hin : (a - dst).toNat < len
    · have hfp : fp a = true := decide_eq_true hin
      rw [tightenMem_perm_in hfp]
      exact (Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hin)).1
    · simp only [hin, ↓reduceIte] at hp; cases hp
  · intro a hp
    dsimp only [m1, Memory.perm, Perm.rwx, Perm.rw, Perm.protNone] at hp
    by_cases hin : (a - dst).toNat < len
    · simp only [hin, ↓reduceIte] at hp; cases hp
    · simp only [hin, ↓reduceIte] at hp; cases hp
  · intro a hr
    dsimp only [m1, Memory.perm, Option.r] at hr
    by_cases hin : (a - dst).toNat < len
    · have hfp : fp a = true := decide_eq_true hin
      rw [tightenMem_perm_in hfp, (Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hin)).1]; rfl
    · simp only [hin, ↓reduceIte] at hr; cases hr
  · intro a hmp
    dsimp only [m1, Memory.perm] at hmp
    by_cases hin : (a - dst).toNat < len
    · have hfp : fp a = true := decide_eq_true hin
      rw [tightenMem_perm_in hfp, (Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hin)).1]; rfl
    · simp only [hin, ↓reduceIte] at hmp; cases hmp
  · intro a han
    dsimp only [m1, Memory.isAnon] at han
    by_cases hin : (a - dst).toNat < len
    · have hfp : fp a = true := decide_eq_true hin
      apply tightenMem_isAnon_of_mapped
      rw [tightenMem_perm_in hfp, (Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hin)).1]; rfl
    · simp only [hin, ↓reduceIte] at han; cases han

private theorem not_inRegion_of_disjointRegions {b₁ b₂ a : BitVec 64} {n : Nat}
    (hdisj : n = 0 ∨ DisjointRegions b₁ n b₂ n) (hn : n < 2 ^ 64)
    (h1 : InRegion b₁ n a) (h2 : InRegion b₂ n a) : False := by
  rcases hdisj with rfl | ⟨hd1, hd2⟩
  · simp [InRegion] at h1
  · dsimp [InRegion] at h1 h2
    bv_omega

/-- Construct `tightenMem fp m ⊨ memRegion dst bs.length ∗ (src ↦ᵣ bs)` from `m.RW dst bs.length`,
    `m.Readable src bs.length`, `bs.length = 0 ∨ DisjointRegions dst bs.length src bs.length`, and
    `m.readBytes src bs.length = bs` (`0` `import all`). -/
theorem satisfies_memcpyRO_tight {m : Memory} {dst src : BitVec 64} {bs : List (BitVec 8)}
    (hrw : m.RW dst bs.length)
    (hreadable : m.Readable src bs.length)
    (hdisj : bs.length = 0 ∨ DisjointRegions dst bs.length src bs.length)
    (hread : m.readBytes src bs.length = bs)
    (hlen : bs.length < 2 ^ 64) :
    let fp := fun a => decide (InRegion dst bs.length a)
    tightenMem fp m ⊨ memRegion dst bs.length ∗ (src ↦ᵣ bs) := by
  intro fp
  let m' := tightenMem fp m
  let m_unm : Memory := ⟨fun a => some (none, m'.read8 a)⟩
  have hcanMap : m_unm.canMap dst bs.length = true := by
    rw [Memory.canMap, Memory.allPerm_iff]; intro _ _; rfl
  have hm0 : m_unm.mapZero dst bs.length ⊨ memRegion dst bs.length ∗ emp :=
    Satisfies.mapZero (satisfies_emp m_unm) hcanMap
  let m1 : Memory :=
    ⟨fun a => if (a - dst).toNat < bs.length then some (some Perm.rw, m'.read8 a) else some (none, m'.read8 a)⟩
  have hm'_read_src : ∀ a, InRegion src bs.length a → m'.read8 a = m.read8 a := by
    intro a hsrc
    have hnot : fp a = false :=
      decide_eq_false (fun hdst => not_inRegion_of_disjointRegions hdisj hlen hdst hsrc)
    obtain ⟨hr_a, hlf_a⟩ := hreadable a hsrc
    dsimp only [m', tightenMem, Memory.read8]
    simp only [hnot, Bool.false_eq_true, ↓reduceIte]
    dsimp only [Memory.perm, Memory.isLazyFree, Perm.rwx, Option.r] at hr_a hlf_a
    rcases hc : m.cells a with _ | ⟨_ | p, b⟩
    · rfl
    · rw [hc] at hr_a; cases hr_a
    · rw [hc] at hr_a hlf_a
      dsimp only [Option.r] at hr_a hlf_a ⊢
      have hok : (p.r && !p.lazyFree) = true := by simp [hr_a, hlf_a]
      simp only [hok, ↓reduceIte]
  have hag : AgreesOutside (m_unm.mapZero dst bs.length) m1 dst bs.length := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a hout
      have hnot : ¬ (a - dst).toNat < bs.length := Nat.not_lt.mpr hout
      dsimp only [m1, m_unm, Memory.mapZero, Memory.read8, Memory.perm, Option.mapped]
      simp only [hnot, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · funext a
      dsimp only [m1, m_unm, Memory.mapZero, Memory.perm, Option.mapped, Perm.rwx, Perm.rw]
      by_cases h : (a - dst).toNat < bs.length
      · simp only [h, decide_true, ↓reduceIte]; rfl
      · simp only [h, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · intro a _
      dsimp only [m1, m_unm, Memory.mapZero, Memory.isLazyFree, Memory.perm, Option.mapped, Perm.rw]
      by_cases h : (a - dst).toNat < bs.length
      · simp only [h, decide_true, ↓reduceIte]; rfl
      · simp only [h, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · intro a _
      dsimp only [m1, Memory.isLazyFree, Perm.rw]
      by_cases h : (a - dst).toNat < bs.length <;> simp only [h, ↓reduceIte]
    · intro a han
      dsimp only [m1, m_unm, Memory.mapZero, Memory.isAnon, Memory.perm, Option.mapped, Perm.rw] at han ⊢
      by_cases h : (a - dst).toNat < bs.length
      · simp only [h, ↓reduceIte]
      · simp only [h, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at han
  have hm1_emp : m1 ⊨ memRegion dst bs.length ∗ emp :=
    (IsBlock.memRegion dst bs.length).update (IsBlock.memRegion dst bs.length) (Nat.le_refl _) hm0 hag trivial
  have hm1 : m1 ⊨ memRegion dst bs.length := by rwa [sepConj_emp] at hm1_emp
  let m2 := m1.mapFresh src bs.length Perm.ro
  have hm2_dst : m2 ⊨ memRegion dst bs.length :=
    satisfies_mapFresh hm1 src bs.length Perm.ro
  have hm2_read8 : ∀ a, m2.read8 a = m'.read8 a := by
    intro a
    rw [Memory.read8_mapFresh]
    dsimp only [m1, Memory.read8]
    by_cases h : (a - dst).toNat < bs.length <;> simp only [h, ↓reduceIte]
  have hro_m2 : m2.RO src bs.length := by
    intro a hsrc
    have hnot_dst : ¬ (a - dst).toNat < bs.length := fun hdst =>
      not_inRegion_of_disjointRegions hdisj hlen hdst hsrc
    have hunm1 : (m1.perm a).mapped = false := by
      dsimp only [m1, Memory.perm, Option.mapped]
      simp only [hnot_dst, ↓reduceIte]; rfl
    have hsrc' : (a - src).toNat < bs.length := hsrc
    refine ⟨?_, ?_⟩
    · dsimp only [m2]; rw [Memory.perm_mapFresh]
      simp only [hsrc', decide_true, hunm1, Bool.not_false, Bool.and_self, ↓reduceIte, Perm.rwx, Perm.ro]
    · dsimp only [m2]; rw [Memory.isLazyFree_mapFresh]
      simp only [hsrc', decide_true, hunm1, Bool.not_false, Bool.and_self, ↓reduceIte, Perm.ro]
  have hread_eq_sub : ∀ (b : BitVec 64) (n : Nat),
      (∀ k < n, m2.read8 (b + BitVec.ofNat 64 k) = m.read8 (b + BitVec.ofNat 64 k)) →
      m2.readBytes b n = m.readBytes b n := by
    intro b n
    induction n generalizing b with
    | zero => intro _; rfl
    | succ n ih =>
      intro hk
      have h0 := hk 0 (Nat.zero_lt_succ n)
      have hz : b + BitVec.ofNat 64 0 = b := by simp
      rw [hz] at h0
      simp only [Memory.readBytes, h0, List.cons.injEq, true_and]
      refine ih (b + 1#64) fun k hlt => ?_
      have he : (b + 1#64) + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (k + 1) := by
        rw [BitVec.add_assoc]; congr 1
        change 1#64 + BitVec.ofNat 64 k = BitVec.ofNat 64 (k + 1)
        bv_omega
      rw [he]
      exact hk (k + 1) (Nat.succ_lt_succ hlt)
  have hread_m2 : m2.readBytes src bs.length = bs := by
    rw [hread_eq_sub src bs.length]
    · exact hread
    · intro k hk
      have hin_src : InRegion src bs.length (src + BitVec.ofNat 64 k) := by
        dsimp [InRegion]; bv_omega
      rw [hm2_read8, hm'_read_src _ hin_src]
  have hm2_both : m2 ⊨ memRegion dst bs.length ∗ (src ↦ᵣ bs) := by
    rw [sepConj_comm]
    exact Satisfies.rodata_intro hro_m2 hread_m2 (Nat.le_of_lt hlen) hm2_dst
  have hlf_m' : ∀ a, m'.isLazyFree a = false := by
    refine tightenMem_isLazyFree_eq_false (fun a hfp => ?_)
    exact (Memory.permNoLazy_eq_some_rw_iff.mp (hrw a (of_decide_eq_true hfp))).2
  refine Arm64.Satisfies.of_perm_mono (fun a => (hm2_read8 a).symm) ?_ ?_ ?_ ?_
    (fun a _ => hlf_m' a) ?_ hm2_both
  · intro a hp
    dsimp only [m2] at hp; rw [Memory.perm_mapFresh] at hp
    by_cases hdst : (a - dst).toNat < bs.length
    · rw [tightenMem_perm_in (decide_eq_true hdst)]
      exact (Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hdst)).1
    · have hunm1 : m1.perm a = none := by
        dsimp only [m1, Memory.perm]; simp only [hdst, ↓reduceIte]
      rw [hunm1] at hp
      by_cases hsrc : (a - src).toNat < bs.length
      · simp only [hsrc, decide_true, Option.mapped, Option.isSome_none, Bool.not_false,
          Bool.and_self, ↓reduceIte, Perm.rwx, Perm.ro, Perm.rw] at hp
        cases hp
      · simp only [hsrc, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hp
        cases hp
  · intro a hp
    dsimp only [m2] at hp; rw [Memory.perm_mapFresh] at hp
    by_cases hdst : (a - dst).toNat < bs.length
    · have hm1p : m1.perm a = some Perm.rw := by
        dsimp only [m1, Memory.perm, Perm.rwx, Perm.rw]; simp only [hdst, ↓reduceIte]
      rw [hm1p] at hp
      simp only [Option.mapped, Option.isSome_some, Bool.not_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, Perm.rwx, Perm.rw, Perm.protNone] at hp
      cases hp
    · have hunm1 : m1.perm a = none := by
        dsimp only [m1, Memory.perm]; simp only [hdst, ↓reduceIte]
      rw [hunm1] at hp
      by_cases hsrc : (a - src).toNat < bs.length
      · simp only [hsrc, decide_true, Option.mapped, Option.isSome_none, Bool.not_false,
          Bool.and_self, ↓reduceIte, Perm.rwx, Perm.ro, Perm.protNone] at hp
        cases hp
      · simp only [hsrc, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hp
        cases hp
  · intro a hr
    dsimp only [m2] at hr; rw [Memory.perm_mapFresh] at hr
    by_cases hdst : (a - dst).toNat < bs.length
    · rw [tightenMem_perm_in (decide_eq_true hdst), (Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hdst)).1]; rfl
    · have hunm1 : m1.perm a = none := by
        dsimp only [m1, Memory.perm]; simp only [hdst, ↓reduceIte]
      rw [hunm1] at hr
      by_cases hsrc : (a - src).toNat < bs.length
      · obtain ⟨hr_s, hlf_s⟩ := hreadable a hsrc
        have hnot_fp : fp a = false := decide_eq_false hdst
        dsimp only [m', tightenMem, Memory.perm, Perm.rwx]
        simp only [hnot_fp, Bool.false_eq_true, ↓reduceIte]
        dsimp only [Memory.perm, Memory.isLazyFree, Perm.rwx, Option.r] at hr_s hlf_s
        rcases hc : m.cells a with _ | ⟨_ | p, b⟩ <;> rw [hc] at hr_s hlf_s
        · cases hr_s
        · cases hr_s
        · dsimp only [Option.r] at hr_s hlf_s ⊢
          have hok : (p.r && !p.lazyFree) = true := by simp [hr_s, hlf_s]
          simp only [hok, ↓reduceIte]
      · simp only [hsrc, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.r] at hr
  · intro a hmp
    dsimp only [m2] at hmp; rw [Memory.perm_mapFresh] at hmp
    by_cases hdst : (a - dst).toNat < bs.length
    · rw [tightenMem_perm_in (decide_eq_true hdst), (Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hdst)).1]; rfl
    · have hunm1 : m1.perm a = none := by
        dsimp only [m1, Memory.perm]; simp only [hdst, ↓reduceIte]
      rw [hunm1] at hmp
      by_cases hsrc : (a - src).toNat < bs.length
      · obtain ⟨hr_s, hlf_s⟩ := hreadable a hsrc
        have hnot_fp : fp a = false := decide_eq_false hdst
        dsimp only [m', tightenMem, Memory.perm, Perm.rwx]
        simp only [hnot_fp, Bool.false_eq_true, ↓reduceIte]
        dsimp only [Memory.perm, Memory.isLazyFree, Perm.rwx, Option.r] at hr_s hlf_s
        rcases hc : m.cells a with _ | ⟨_ | p, b⟩ <;> rw [hc] at hr_s hlf_s
        · cases hr_s
        · cases hr_s
        · dsimp only at hr_s hlf_s ⊢
          have hok : (p.r && !p.lazyFree) = true := by simp [hr_s, hlf_s]
          simp only [hok, ↓reduceIte]; rfl
      · simp only [hsrc, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hmp
        cases hmp
  · intro a han
    dsimp only [m2] at han; rw [Memory.isAnon_mapFresh] at han
    apply tightenMem_isAnon_of_mapped
    by_cases hdst : (a - dst).toNat < bs.length
    · rw [tightenMem_perm_in (decide_eq_true hdst), (Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hdst)).1]; rfl
    · have hunm1 : m1.perm a = none := by
        dsimp only [m1, Memory.perm]; simp only [hdst, ↓reduceIte]
      have han1 : m1.isAnon a = false := by
        dsimp only [m1, Memory.isAnon]; simp only [hdst, ↓reduceIte]
      rw [hunm1, han1] at han
      by_cases hsrc : (a - src).toNat < bs.length
      · obtain ⟨hr_s, hlf_s⟩ := hreadable a hsrc
        have hnot_fp : fp a = false := decide_eq_false hdst
        dsimp only [m', tightenMem, Memory.perm, Perm.rwx]
        simp only [hnot_fp, Bool.false_eq_true, ↓reduceIte]
        dsimp only [Memory.perm, Memory.isLazyFree, Perm.rwx, Option.r] at hr_s hlf_s
        rcases hc : m.cells a with _ | ⟨_ | p, b⟩ <;> rw [hc] at hr_s hlf_s
        · cases hr_s
        · cases hr_s
        · dsimp only at hr_s hlf_s ⊢
          have hok : (p.r && !p.lazyFree) = true := by simp [hr_s, hlf_s]
          simp only [hok, ↓reduceIte]; rfl
      · simp only [hsrc, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.or_false] at han

/-! ### 6b. Lockstep `execInst` Simulation Between `tightenMem` View and Real `State` -/

private structure MemTightInv (fp : BitVec 64 → Bool) (m0 m m_tight : Memory) : Prop where
  tight_eq : m_tight = tightenMem fp m
  outside_eq : ∀ a, fp a = false → m.cells a = m0.cells a
  perm_eq : m.perm = m0.perm
  lf_imp : ∀ a, m0.isLazyFree a = false → m.isLazyFree a = false
  anon_eq : m.isAnon = m0.isAnon

private theorem memTightInv_refl (fp : BitVec 64 → Bool) (m0 : Memory) :
    MemTightInv fp m0 m0 (tightenMem fp m0) :=
  ⟨rfl, fun _ _ => rfl, rfl, fun _ h => h, rfl⟩

private theorem memTightInv_write8 {fp : BitVec 64 → Bool} {m0 m m_tight : Memory}
    (hinv : MemTightInv fp m0 m m_tight) {addr : BitVec 64} (val : BitVec 8)
    (hfp : fp addr = true) :
    MemTightInv fp m0 (m.write8 addr val) (m_tight.write8 addr val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hinv.tight_eq]
    apply Memory.ext; funext x
    by_cases hx : x = addr
    · subst hx
      dsimp [Memory.write8, tightenMem, Memory.rawPerm]
      simp only [hfp, ↓reduceIte]
      rcases m.cells x with _ | ⟨_ | p, b⟩ <;> rfl
    · dsimp [Memory.write8, tightenMem]
      simp only [hx, ↓reduceIte]
  · intro x hfx
    have hx : x ≠ addr := by intro heq; subst heq; rw [hfp] at hfx; contradiction
    dsimp [Memory.write8]; simp only [hx, ↓reduceIte]; exact hinv.outside_eq x hfx
  · funext x
    by_cases hx : x = addr
    · subst hx
      have hp := congrFun hinv.perm_eq x
      dsimp only [Memory.write8, Memory.perm, Memory.rawPerm, Perm.rwx] at hp ⊢
      simp only [↓reduceIte]
      revert hp
      rcases m.cells x with _ | ⟨_ | p, b⟩ <;> intro hp <;> exact hp
    · dsimp only [Memory.write8, Memory.perm]
      simp only [hx, ↓reduceIte]; exact congrFun hinv.perm_eq x
  · intro x hlf0
    dsimp [Memory.write8, Memory.isLazyFree, Memory.rawPerm]
    by_cases hx : x = addr
    · subst hx; simp only [↓reduceIte]; rcases m.cells x with _ | ⟨_ | p, b⟩ <;> rfl
    · simp only [hx, ↓reduceIte]; exact hinv.lf_imp x hlf0
  · funext x
    by_cases hx : x = addr
    · subst hx
      have ha := congrFun hinv.anon_eq x
      dsimp only [Memory.write8, Memory.isAnon, Memory.rawPerm] at ha ⊢
      simp only [↓reduceIte]
      revert ha
      rcases m.cells x with _ | ⟨_ | p, b⟩ <;> intro ha <;> exact ha
    · dsimp only [Memory.write8, Memory.isAnon]
      simp only [hx, ↓reduceIte]; exact congrFun hinv.anon_eq x

private theorem memTightInv_writeSized {fp : BitVec 64 → Bool} {m0 m m_tight : Memory}
    (hinv : MemTightInv fp m0 m m_tight) {sz : MemWidth} {ea : BitVec 64} (val : BitVec 64)
    (hfp : ∀ k < sz.bytes, fp (ea + BitVec.ofNat 64 k) = true) :
    MemTightInv fp m0 (m.writeSized sz ea val) (m_tight.writeSized sz ea val) := by
  cases sz with
  | B8 =>
    have h0 := hfp 0 (by decide)
    have hz : ea + BitVec.ofNat 64 0 = ea := by simp
    rw [hz] at h0
    exact memTightInv_write8 hinv _ h0
  | H16 =>
    exact memTightInv_write8 (memTightInv_write8 hinv _ (hfp 0 (by decide))) _ (hfp 1 (by decide))
  | W32 =>
    exact memTightInv_write8 (memTightInv_write8 (memTightInv_write8 (memTightInv_write8 hinv
      _ (hfp 0 (by decide))) _ (hfp 1 (by decide))) _ (hfp 2 (by decide))) _ (hfp 3 (by decide))
  | X64 =>
    exact memTightInv_write8 (memTightInv_write8 (memTightInv_write8 (memTightInv_write8
      (memTightInv_write8 (memTightInv_write8 (memTightInv_write8 (memTightInv_write8 hinv
      _ (hfp 0 (by decide))) _ (hfp 1 (by decide))) _ (hfp 2 (by decide))) _ (hfp 3 (by decide)))
      _ (hfp 4 (by decide))) _ (hfp 5 (by decide))) _ (hfp 6 (by decide))) _ (hfp 7 (by decide))

private theorem memTightInv_writeSimdSized {fp : BitVec 64 → Bool} {m0 m m_tight : Memory}
    (hinv : MemTightInv fp m0 m m_tight) {sz : SimdMemSize} {ea : BitVec 64} (val : BitVec 128)
    (hfp : ∀ k < sz.bytes, fp (ea + BitVec.ofNat 64 k) = true) :
    MemTightInv fp m0 (m.writeSimdSized sz ea val) (m_tight.writeSimdSized sz ea val) := by
  cases sz with
  | B8 =>
    have h0 := hfp 0 (by decide)
    have hz : ea + BitVec.ofNat 64 0 = ea := by simp
    rw [hz] at h0
    exact memTightInv_write8 hinv _ h0
  | H16 =>
    exact memTightInv_write8 (memTightInv_write8 hinv _ (hfp 0 (by decide))) _ (hfp 1 (by decide))
  | S32 =>
    exact memTightInv_write8 (memTightInv_write8 (memTightInv_write8 (memTightInv_write8 hinv
      _ (hfp 0 (by decide))) _ (hfp 1 (by decide))) _ (hfp 2 (by decide))) _ (hfp 3 (by decide))
  | D64 =>
    exact memTightInv_write8 (memTightInv_write8 (memTightInv_write8 (memTightInv_write8
      (memTightInv_write8 (memTightInv_write8 (memTightInv_write8 (memTightInv_write8 hinv
      _ (hfp 0 (by decide))) _ (hfp 1 (by decide))) _ (hfp 2 (by decide))) _ (hfp 3 (by decide)))
      _ (hfp 4 (by decide))) _ (hfp 5 (by decide))) _ (hfp 6 (by decide))) _ (hfp 7 (by decide))
  | Q128 =>
    have hlo : MemTightInv fp m0 (m.write64 ea (val.extractLsb' 0 64))
        (m_tight.write64 ea (val.extractLsb' 0 64)) :=
      memTightInv_writeSized (sz := .X64) hinv _
        (fun k hk => hfp k (by dsimp [MemWidth.bytes, SimdMemSize.bytes] at hk ⊢; omega))
    have hhi_fp : ∀ k < 8, fp ((ea + 8#64) + BitVec.ofNat 64 k) = true := by
      intro k hk
      have he : (ea + 8#64) + BitVec.ofNat 64 k = ea + BitVec.ofNat 64 (8 + k) := by
        rw [BitVec.add_assoc]; congr 1
        change 8#64 + BitVec.ofNat 64 k = BitVec.ofNat 64 (8 + k)
        bv_omega
      rw [he]
      exact hfp (8 + k) (by dsimp [SimdMemSize.bytes]; omega)
    exact memTightInv_writeSized (sz := .X64) hlo _ hhi_fp

private theorem memTightInv_simdStoreRegs {fp : BitVec 64 → Bool} {sz : SimdMemSize}
    (rd : BitVec 5 → BitVec 128) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) {m0 m m_tight : Memory},
      MemTightInv fp m0 m m_tight →
      (∀ k < n * sz.bytes, fp (ea + BitVec.ofNat 64 k) = true) →
      MemTightInv fp m0 (simdStoreRegs sz rd n vt ea m) (simdStoreRegs sz rd n vt ea m_tight)
  | 0, _, _, _, _, _, hinv, _ => hinv
  | n + 1, vt, ea, _, _, _, hinv, hfp => by
    have h0 : ∀ k < sz.bytes, fp (ea + BitVec.ofNat 64 k) = true :=
      fun k hk => hfp k (by have : 1 * sz.bytes ≤ (n + 1) * sz.bytes := Nat.mul_le_mul_right _ (by omega); omega)
    have hstep := memTightInv_writeSimdSized hinv (rd vt) h0
    refine memTightInv_simdStoreRegs rd n (vt + 1#5) (ea + BitVec.ofNat 64 sz.bytes) hstep fun k hk => ?_
    have he : (ea + BitVec.ofNat 64 sz.bytes) + BitVec.ofNat 64 k = ea + BitVec.ofNat 64 (sz.bytes + k) := by
      rw [BitVec.add_assoc]; congr 1
      rw [← BitVec.ofNat_add]
    rw [he]
    exact hfp (sz.bytes + k) (by rw [Nat.succ_mul, Nat.add_comm]; omega)

private def sysProj (s : State) :=
  (s.tpidrEl0, s.fpsr, s.brkStart, s.brk, s.fs, s.oracle, s.oracleIdx,
   s.exclFails, s.trace, s.symtab, s.sigActions, s.sigAltStack, s.physMemAvail)

private structure StateTightRel (fp : BitVec 64 → Bool) (gprOk vregOk : BitVec 5 → Bool)
    (s0 st st_tight : State) : Prop where
  tight_eq : st_tight = { st with sp := 0#64, mem := tightenMem fp st.mem }
  run_st : st.status = .Running
  sp_eq : st.sp = s0.sp
  regs_eq : ∀ idx : BitVec 5, gprOk idx = false → st.regs.regs idx = s0.regs.regs idx
  vregs_eq : ∀ idx : BitVec 5, vregOk idx = false → st.vregs.regs idx = s0.vregs.regs idx
  mem_inv : MemTightInv fp s0.mem st.mem st_tight.mem
  sys_eq : sysProj st = sysProj s0

private theorem stateTightRel_refl (fp : BitVec 64 → Bool) (gprOk vregOk : BitVec 5 → Bool)
    (s0 : State) (hrun : s0.status = .Running) :
    StateTightRel fp gprOk vregOk s0 s0 { s0 with sp := 0#64, mem := tightenMem fp s0.mem } :=
  ⟨rfl, hrun, rfl, fun _ _ => rfl, fun _ _ => rfl, memTightInv_refl fp s0.mem, rfl⟩

private theorem readReg64_tight_of_noSp {fp : BitVec 64 → Bool} {st : State} {r : Reg}
    (hr : regReadNoSp r = true) :
    ({ st with sp := 0#64, mem := tightenMem fp st.mem } : State).readReg64 r = st.readReg64 r := by
  cases r with
  | gpr _ => rfl
  | sp => simp [regReadNoSp] at hr
  | xzr => rfl

private theorem readReg_tight_of_noSp {fp : BitVec 64 → Bool} {st : State} (w : Width) {r : Reg}
    (hr : regReadNoSp r = true) :
    ({ st with sp := 0#64, mem := tightenMem fp st.mem } : State).readReg w r = st.readReg w r := by
  cases w <;> simp [State.readReg, State.readReg32, readReg64_tight_of_noSp hr]

private theorem checkRegSPAligned_of_noSp (s : State) {r : Reg} (hr : regReadNoSp r = true) :
    checkRegSPAligned s r = true := by
  cases r with
  | gpr _ => rfl
  | sp => simp [regReadNoSp] at hr
  | xzr => rfl

private theorem evalAddrMode_tight_of_addrOk {fp : BitVec 64 → Bool} {gprOk : BitVec 5 → Bool}
    {st : State} {addr : AddrMode} (ha : addrOk gprOk addr = true) :
    checkAddrSPAligned ({ st with sp := 0#64, mem := tightenMem fp st.mem }) addr = true ∧
    checkAddrSPAligned st addr = true ∧
    evalAddrMode ({ st with sp := 0#64, mem := tightenMem fp st.mem }) addr = evalAddrMode st addr ∧
    (∀ b nb, (evalAddrMode st addr).2 = some (b, nb) → regWriteOk gprOk b = true) := by
  cases addr with
  | Offset b off | UnscaledOffset b off =>
    dsimp [addrOk] at ha
    refine ⟨checkRegSPAligned_of_noSp _ ha, checkRegSPAligned_of_noSp _ ha, ?_, fun _ _ h => by cases h⟩
    simp [evalAddrMode, readReg64_tight_of_noSp ha]
  | PreIndex b off | PostIndex b off =>
    dsimp [addrOk] at ha; simp only [Bool.and_eq_true] at ha
    refine ⟨checkRegSPAligned_of_noSp _ ha.1, checkRegSPAligned_of_noSp _ ha.1, ?_, fun b' _ h => ?_⟩
    · simp [evalAddrMode, readReg64_tight_of_noSp ha.1]
    · simp only [evalAddrMode, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact ha.2
  | RegOffset b idx ext amt =>
    dsimp [addrOk] at ha; simp only [Bool.and_eq_true] at ha
    refine ⟨checkRegSPAligned_of_noSp _ ha.1, checkRegSPAligned_of_noSp _ ha.1, ?_, fun _ _ h => by cases h⟩
    simp [evalAddrMode, readReg64_tight_of_noSp ha.1, readReg64_tight_of_noSp ha.2]

private theorem stateTightRel_advancePC {fp : BitVec 64 → Bool} {gprOk vregOk : BitVec 5 → Bool}
    {s0 st st_tight : State} (hrel : StateTightRel fp gprOk vregOk s0 st st_tight) :
    StateTightRel fp gprOk vregOk s0 st.advancePC st_tight.advancePC := by
  rcases hrel with ⟨rfl, hrun, hsp, hregs, hvregs, hmem, hsys⟩
  exact ⟨rfl, hrun, hsp, hregs, hvregs, hmem, by cases st; exact hsys⟩

private theorem stateTightRel_setPC {fp : BitVec 64 → Bool} {gprOk vregOk : BitVec 5 → Bool}
    {s0 st st_tight : State} (hrel : StateTightRel fp gprOk vregOk s0 st st_tight) (pc' : BitVec 64) :
    StateTightRel fp gprOk vregOk s0 (st.setPC pc') (st_tight.setPC pc') := by
  rcases hrel with ⟨rfl, hrun, hsp, hregs, hvregs, hmem, hsys⟩
  exact ⟨rfl, hrun, hsp, hregs, hvregs, hmem, by cases st; exact hsys⟩

private theorem stateTightRel_setPState {fp : BitVec 64 → Bool} {gprOk vregOk : BitVec 5 → Bool}
    {s0 st st_tight : State} (hrel : StateTightRel fp gprOk vregOk s0 st st_tight) (ps : PState) :
    StateTightRel fp gprOk vregOk s0 (st.setPState ps) (st_tight.setPState ps) := by
  rcases hrel with ⟨rfl, hrun, hsp, hregs, hvregs, hmem, hsys⟩
  exact ⟨rfl, hrun, hsp, hregs, hvregs, hmem, by cases st; exact hsys⟩

private theorem stateTightRel_writeReg64 {fp : BitVec 64 → Bool} {gprOk vregOk : BitVec 5 → Bool}
    {s0 st st_tight : State} (hrel : StateTightRel fp gprOk vregOk s0 st st_tight)
    {rd : Reg} (val : BitVec 64) (hrd : regWriteOk gprOk rd = true) :
    StateTightRel fp gprOk vregOk s0 (st.writeReg64 rd val) (st_tight.writeReg64 rd val) := by
  rcases hrel with ⟨rfl, hrun, hsp, hregs, hvregs, hmem, hsys⟩
  cases rd with
  | sp => simp [regWriteOk] at hrd
  | xzr =>
    exact ⟨rfl, hrun, hsp, hregs, hvregs, hmem, by cases st; exact hsys⟩
  | gpr b =>
    dsimp [regWriteOk] at hrd
    refine ⟨rfl, hrun, hsp, fun idx hidx => ?_, hvregs, hmem, by cases st; exact hsys⟩
    dsimp [State.writeReg64]
    by_cases hb31 : b == 31#5
    · simp [hb31, hregs idx hidx]
    · simp only [hb31, ↓reduceIte, RegFile.write]
      simp only [hb31, Bool.false_or] at hrd
      have hne : idx ≠ b := by intro heq; subst heq; rw [hrd] at hidx; contradiction
      simp [hne, hregs idx hidx]

private theorem stateTightRel_writeReg {fp : BitVec 64 → Bool} {gprOk vregOk : BitVec 5 → Bool}
    {s0 st st_tight : State} (hrel : StateTightRel fp gprOk vregOk s0 st st_tight)
    (w : Width) {rd : Reg} (val : BitVec 64) (hrd : regWriteOk gprOk rd = true) :
    StateTightRel fp gprOk vregOk s0 (st.writeReg w rd val) (st_tight.writeReg w rd val) :=
  stateTightRel_writeReg64 hrel _ hrd

private theorem stateTightRel_writeVReg128 {fp : BitVec 64 → Bool} {gprOk vregOk : BitVec 5 → Bool}
    {s0 st st_tight : State} (hrel : StateTightRel fp gprOk vregOk s0 st st_tight)
    {rd : BitVec 5} (val : BitVec 128) (hrd : vregOk rd = true) :
    StateTightRel fp gprOk vregOk s0 (st.writeVReg128 rd val) (st_tight.writeVReg128 rd val) := by
  rcases hrel with ⟨rfl, hrun, hsp, hregs, hvregs, hmem, hsys⟩
  refine ⟨rfl, hrun, hsp, hregs, fun idx hidx => ?_, hmem, by cases st; exact hsys⟩
  dsimp [State.writeVReg128, VRegFile.write]
  have hne : idx ≠ rd := by intro heq; subst heq; rw [hrd] at hidx; contradiction
  simp [hne, hvregs idx hidx]

private theorem stateTightRel_setMem {fp : BitVec 64 → Bool} {gprOk vregOk : BitVec 5 → Bool}
    {s0 st st_tight : State} (hrel : StateTightRel fp gprOk vregOk s0 st st_tight)
    {m' m_tight' : Memory} (hmem' : MemTightInv fp s0.mem m' m_tight') :
    StateTightRel fp gprOk vregOk s0 (st.setMem m') (st_tight.setMem m_tight') := by
  rcases hrel with ⟨rfl, hrun, hsp, hregs, hvregs, _, hsys⟩
  exact ⟨by rw [hmem'.tight_eq]; rfl, hrun, hsp, hregs, hvregs, hmem', by cases st; exact hsys⟩

private theorem execInst_stateTightRel_step {fp : BitVec 64 → Bool} {gprOk vregOk : BitVec 5 → Bool}
    {s0 st st_tight : State} {inst : Instr}
    (hrel : StateTightRel fp gprOk vregOk s0 st st_tight)
    (hallow : instrAllowed gprOk vregOk inst = true)
    (hrun_next : (execInst inst st_tight).status = .Running) :
    StateTightRel fp gprOk vregOk s0 (execInst inst st) (execInst inst st_tight) := by
  have ht_eq := hrel.tight_eq
  cases inst with
  | adr page rd off =>
    dsimp [instrAllowed] at hallow
    have hpc : st_tight.pc = st.pc := by rw [ht_eq]
    dsimp only [execInst, execInstWithSvc]; rw [hpc]
    exact stateTightRel_advancePC (stateTightRel_writeReg64 hrel _ hallow)
  | moveWide w op rd imm16 hw =>
    dsimp [instrAllowed] at hallow
    dsimp only [execInst, execInstWithSvc, execMoveWide]
    have hnsp : regReadNoSp rd = true := by cases rd <;> simp [regWriteOk, regReadNoSp] at hallow ⊢
    have hrd_r : st_tight.readReg w rd = st.readReg w rd := by
      rw [ht_eq]; exact readReg_tight_of_noSp w hnsp
    cases op <;> simp only [hrd_r] <;>
      exact stateTightRel_advancePC (stateTightRel_writeReg hrel w _ hallow)
  | addSubImm w op rd rn imm12 sh12 =>
    dsimp [instrAllowed] at hallow; simp only [Bool.and_eq_true] at hallow
    dsimp only [execInst, execInstWithSvc, execAddSubImm]
    have hrn : st_tight.readReg w rn = st.readReg w rn := by rw [ht_eq]; exact readReg_tight_of_noSp w hallow.1
    rw [hrn]
    rcases evalAddSub w op (st.readReg w rn) (if sh12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64) none with ⟨res, _ | ps⟩
    · exact stateTightRel_advancePC (stateTightRel_writeReg hrel w res hallow.2)
    · exact stateTightRel_advancePC (stateTightRel_setPState (stateTightRel_writeReg hrel w res hallow.2) ps)
  | logicalImm w op rd rn mask =>
    dsimp [instrAllowed] at hallow; simp only [Bool.and_eq_true] at hallow
    dsimp only [execInst, execInstWithSvc, execLogicalImm]
    have hrn : st_tight.readReg w rn = st.readReg w rn := by rw [ht_eq]; exact readReg_tight_of_noSp w hallow.1
    have hps : st_tight.pstate = st.pstate := by rw [ht_eq]
    rw [hrn, hps]
    rcases evalLogical w op (st.readReg w rn) mask st.pstate with ⟨res, _ | ps⟩
    · exact stateTightRel_advancePC (stateTightRel_writeReg hrel w res hallow.2)
    · exact stateTightRel_advancePC (stateTightRel_setPState (stateTightRel_writeReg hrel w res hallow.2) ps)
  | bitfield w op rd rn immr imms =>
    dsimp [instrAllowed] at hallow; simp only [Bool.and_eq_true] at hallow
    have hnsp_rd : regReadNoSp rd = true := by cases rd <;> simp [regWriteOk, regReadNoSp] at hallow ⊢
    dsimp only [execInst, execInstWithSvc, execBitfield]
    have hrd_r : st_tight.readReg w rd = st.readReg w rd := by rw [ht_eq]; exact readReg_tight_of_noSp w hnsp_rd
    have hrn_r : st_tight.readReg w rn = st.readReg w rn := by rw [ht_eq]; exact readReg_tight_of_noSp w hallow.1
    rw [hrd_r, hrn_r]
    exact stateTightRel_advancePC (stateTightRel_writeReg hrel w _ hallow.2)
  | dataProc1 w op rd rn =>
    dsimp [instrAllowed] at hallow; simp only [Bool.and_eq_true] at hallow
    dsimp only [execInst, execInstWithSvc, execDataProc1]
    have hrn_r : st_tight.readReg w rn = st.readReg w rn := by rw [ht_eq]; exact readReg_tight_of_noSp w hallow.1
    rw [hrn_r]
    exact stateTightRel_advancePC (stateTightRel_writeReg hrel w _ hallow.2)
  | addSubShift w op rd rn rm sh amt =>
    dsimp [instrAllowed] at hallow; simp only [Bool.and_eq_true] at hallow
    rcases hallow with ⟨⟨hrn, hrm⟩, hrd⟩
    dsimp only [execInst, execInstWithSvc, execAddSubShift]
    have hrn_r : st_tight.readReg w rn = st.readReg w rn := by rw [ht_eq]; exact readReg_tight_of_noSp w hrn
    have hrm_r : st_tight.readReg w rm = st.readReg w rm := by rw [ht_eq]; exact readReg_tight_of_noSp w hrm
    rw [hrn_r, hrm_r]
    rcases evalAddSub w op (st.readReg w rn) (shiftVal w (st.readReg w rm) sh amt) none with ⟨res, _ | ps⟩
    · exact stateTightRel_advancePC (stateTightRel_writeReg hrel w res hrd)
    · exact stateTightRel_advancePC (stateTightRel_setPState (stateTightRel_writeReg hrel w res hrd) ps)
  | addSubExt w op rd rn rm ext amt =>
    dsimp [instrAllowed] at hallow; simp only [Bool.and_eq_true] at hallow
    rcases hallow with ⟨⟨hrn, hrm⟩, hrd⟩
    dsimp only [execInst, execInstWithSvc, execAddSubExt]
    have hrn_r : st_tight.readReg w rn = st.readReg w rn := by rw [ht_eq]; exact readReg_tight_of_noSp w hrn
    have hrm_r : st_tight.readReg64 rm = st.readReg64 rm := by rw [ht_eq]; exact readReg64_tight_of_noSp hrm
    rw [hrn_r, hrm_r]
    rcases evalAddSub w op (st.readReg w rn) (extendVal w (st.readReg64 rm) ext amt) none with ⟨res, _ | ps⟩
    · exact stateTightRel_advancePC (stateTightRel_writeReg hrel w res hrd)
    · exact stateTightRel_advancePC (stateTightRel_setPState (stateTightRel_writeReg hrel w res hrd) ps)
  | logicalShift w op rd rn rm sh amt =>
    dsimp [instrAllowed] at hallow; simp only [Bool.and_eq_true] at hallow
    rcases hallow with ⟨⟨hrn, hrm⟩, hrd⟩
    dsimp only [execInst, execInstWithSvc, execLogicalShift]
    have hrn_r : st_tight.readReg w rn = st.readReg w rn := by rw [ht_eq]; exact readReg_tight_of_noSp w hrn
    have hrm_r : st_tight.readReg w rm = st.readReg w rm := by rw [ht_eq]; exact readReg_tight_of_noSp w hrm
    have hps : st_tight.pstate = st.pstate := by rw [ht_eq]
    rw [hrn_r, hrm_r, hps]
    rcases evalLogical w op (st.readReg w rn) (shiftVal w (st.readReg w rm) sh amt) st.pstate with ⟨res, _ | ps⟩
    · exact stateTightRel_advancePC (stateTightRel_writeReg hrel w res hrd)
    · exact stateTightRel_advancePC (stateTightRel_setPState (stateTightRel_writeReg hrel w res hrd) ps)
  | condSelect w op rd rn rm cond =>
    dsimp [instrAllowed] at hallow; simp only [Bool.and_eq_true] at hallow
    rcases hallow with ⟨⟨hrn, hrm⟩, hrd⟩
    dsimp only [execInst, execInstWithSvc, execCondSelect]
    have hrn_r : st_tight.readReg w rn = st.readReg w rn := by rw [ht_eq]; exact readReg_tight_of_noSp w hrn
    have hrm_r : st_tight.readReg w rm = st.readReg w rm := by rw [ht_eq]; exact readReg_tight_of_noSp w hrm
    have hps : st_tight.pstate = st.pstate := by rw [ht_eq]
    rw [hrn_r, hrm_r, hps]
    exact stateTightRel_advancePC (stateTightRel_writeReg hrel w _ hrd)
  | extr w rd rn rm lsb =>
    dsimp [instrAllowed] at hallow; simp only [Bool.and_eq_true] at hallow
    rcases hallow with ⟨⟨hrn, hrm⟩, hrd⟩
    dsimp only [execInst, execInstWithSvc]
    have hrn32 : st_tight.readReg32 rn = st.readReg32 rn := by
      simp [State.readReg32, ht_eq, readReg64_tight_of_noSp hrn]
    have hrm32 : st_tight.readReg32 rm = st.readReg32 rm := by
      simp [State.readReg32, ht_eq, readReg64_tight_of_noSp hrm]
    have hrn64 : st_tight.readReg64 rn = st.readReg64 rn := by rw [ht_eq]; exact readReg64_tight_of_noSp hrn
    have hrm64 : st_tight.readReg64 rm = st.readReg64 rm := by rw [ht_eq]; exact readReg64_tight_of_noSp hrm
    cases w <;> simp only [hrn32, hrm32, hrn64, hrm64] <;>
      exact stateTightRel_advancePC (stateTightRel_writeReg hrel _ _ hrd)
  | dataProc2 w op rd rn rm =>
    dsimp [instrAllowed] at hallow; simp only [Bool.and_eq_true] at hallow
    rcases hallow with ⟨⟨hrn, hrm⟩, hrd⟩
    dsimp only [execInst, execInstWithSvc, execDataProc2]
    have hrn_r : st_tight.readReg w rn = st.readReg w rn := by rw [ht_eq]; exact readReg_tight_of_noSp w hrn
    have hrm_r : st_tight.readReg w rm = st.readReg w rm := by rw [ht_eq]; exact readReg_tight_of_noSp w hrm
    rw [hrn_r, hrm_r]
    exact stateTightRel_advancePC (stateTightRel_writeReg hrel w _ hrd)
  | condCompareReg w isSub rn rm nzcv cond =>
    dsimp [instrAllowed] at hallow; simp only [Bool.and_eq_true] at hallow
    dsimp only [execInst, execInstWithSvc, execCondCompare]
    have hrn_r : st_tight.readReg w rn = st.readReg w rn := by rw [ht_eq]; exact readReg_tight_of_noSp w hallow.1
    have hrm_r : st_tight.readReg w rm = st.readReg w rm := by rw [ht_eq]; exact readReg_tight_of_noSp w hallow.2
    have hps : st_tight.pstate = st.pstate := by rw [ht_eq]
    rw [hrn_r, hrm_r, hps]
    by_cases hc : ConditionHolds cond st.pstate = true
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rcases evalAddSub w (if isSub then .SUBS else .ADDS) (st.readReg w rn) (st.readReg w rm) none with ⟨_, _ | ps⟩
      · exact stateTightRel_advancePC hrel
      · exact stateTightRel_advancePC (stateTightRel_setPState hrel ps)
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact stateTightRel_advancePC (stateTightRel_setPState hrel _)
  | condCompareImm w isSub rn imm5 nzcv cond =>
    dsimp [instrAllowed] at hallow
    dsimp only [execInst, execInstWithSvc, execCondCompare]
    have hrn_r : st_tight.readReg w rn = st.readReg w rn := by rw [ht_eq]; exact readReg_tight_of_noSp w hallow
    have hps : st_tight.pstate = st.pstate := by rw [ht_eq]
    rw [hrn_r, hps]
    by_cases hc : ConditionHolds cond st.pstate = true
    · simp only [hc, ↓reduceIte]
      rcases evalAddSub w (if isSub then .SUBS else .ADDS) (st.readReg w rn) (imm5.zeroExtend 64) none with ⟨_, _ | ps⟩
      · exact stateTightRel_advancePC hrel
      · exact stateTightRel_advancePC (stateTightRel_setPState hrel ps)
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact stateTightRel_advancePC (stateTightRel_setPState hrel _)
  | b off =>
    dsimp only [execInst, execInstWithSvc]
    have hpc : st_tight.pc = st.pc := by rw [ht_eq]
    rw [hpc]; exact stateTightRel_setPC hrel _
  | bCond cond off =>
    dsimp only [execInst, execInstWithSvc]
    have hps : st_tight.pstate = st.pstate := by rw [ht_eq]
    have hpc : st_tight.pc = st.pc := by rw [ht_eq]
    rw [hps, hpc]
    by_cases hc : ConditionHolds cond st.pstate = true
    · simp only [hc, ↓reduceIte]; exact stateTightRel_setPC hrel _
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact stateTightRel_advancePC hrel
  | nop =>
    exact stateTightRel_advancePC hrel
  | br rn | ret rn =>
    dsimp [instrAllowed] at hallow
    dsimp only [execInst, execInstWithSvc]
    have hrn_r : st_tight.readReg64 rn = st.readReg64 rn := by rw [ht_eq]; exact readReg64_tight_of_noSp hallow
    rw [hrn_r]; exact stateTightRel_setPC hrel _
  | cbz w isNZ rt off =>
    dsimp [instrAllowed] at hallow
    dsimp only [execInst, execInstWithSvc]
    have hrt_r : st_tight.readReg w rt = st.readReg w rt := by rw [ht_eq]; exact readReg_tight_of_noSp w hallow
    have hpc : st_tight.pc = st.pc := by rw [ht_eq]
    rw [hrt_r, hpc]
    by_cases hbr : (if isNZ then (st.readReg w rt == 0#64) != true else st.readReg w rt == 0#64) = true
    · simp only [hbr, ↓reduceIte]; exact stateTightRel_setPC hrel _
    · simp only [hbr, Bool.false_eq_true, ↓reduceIte]; exact stateTightRel_advancePC hrel
  | tbz _ isNZ rt bitPos off =>
    dsimp [instrAllowed] at hallow
    dsimp only [execInst, execInstWithSvc]
    have hrt_r : st_tight.readReg64 rt = st.readReg64 rt := by rw [ht_eq]; exact readReg64_tight_of_noSp hallow
    have hpc : st_tight.pc = st.pc := by rw [ht_eq]
    rw [hrt_r, hpc]
    by_cases hbr : ((st.readReg64 rt).getLsbD bitPos == isNZ) = true
    · simp only [hbr, ↓reduceIte]; exact stateTightRel_setPC hrel _
    · simp only [hbr, Bool.false_eq_true, ↓reduceIte]; exact stateTightRel_advancePC hrel
  | dcZva rt =>
    dsimp [instrAllowed] at hallow
    dsimp only [execInst, execInstWithSvc] at hrun_next ⊢
    have hrt_r : st_tight.readReg64 rt = st.readReg64 rt := by rw [ht_eq]; exact readReg64_tight_of_noSp hallow
    rw [hrt_r] at hrun_next ⊢
    have hcw_t : st_tight.mem.canWrite (st.readReg64 rt &&& ~~~63#64) 64 = true := by
      cases hcw : st_tight.mem.canWrite (st.readReg64 rt &&& ~~~63#64) 64
      · rw [hcw] at hrun_next; cases hrun_next
      · rfl
    have ⟨hcw_st, hfp_ea⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_t)
    simp only [hcw_t, hcw_st, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact stateTightRel_advancePC
      (stateTightRel_setMem hrel (memTightInv_simdStoreRegs _ 4 0#5 _ hrel.mem_inv hfp_ea))
  | sysReg isRead sysreg rt =>
    cases isRead
    · cases hallow
    · have hf : instrAllowed gprOk vregOk (.sysReg true sysreg rt) =
          (if sysreg == 0x5807#15 then regWriteOk gprOk rt else false) := rfl
      rw [hf] at hallow
      by_cases hsys : (sysreg == 0x5807#15) = true
      · simp only [hsys, ↓reduceIte] at hallow
        have hsys_eq : sysreg = 0x5807#15 := of_decide_eq_true hsys
        subst hsys_eq
        change StateTightRel fp gprOk vregOk s0 ((st.writeReg64 rt 4#64).advancePC)
          ((st_tight.writeReg64 rt 4#64).advancePC)
        exact stateTightRel_advancePC (stateTightRel_writeReg64 hrel 4#64 hallow)
      · simp only [hsys, Bool.false_eq_true, ↓reduceIte] at hallow
  | ldr w sz sgn rt addr =>
    dsimp [instrAllowed] at hallow; simp only [Bool.and_eq_true] at hallow
    obtain ⟨hsp_t, hsp_s, heval_eq, hwb_ok⟩ := evalAddrMode_tight_of_addrOk (fp := fp) (st := st) hallow.1
    rw [← ht_eq] at hsp_t heval_eq
    dsimp only [execInst, execInstWithSvc, execLdr] at hrun_next ⊢
    simp only [hsp_t, hsp_s, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval_eq] at hrun_next ⊢
    have hcr_t : st_tight.mem.canRead (evalAddrMode st addr).1 sz.bytes = true := by
      cases hcr : st_tight.mem.canRead (evalAddrMode st addr).1 sz.bytes
      · rw [hcr] at hrun_next; cases hrun_next
      · rfl
    have hcr_st := (tightenMem_canRead_imp (hrel.mem_inv.tight_eq ▸ hcr_t)).1
    have hrd_eq : st_tight.mem.readSized sz sgn (evalAddrMode st addr).1 =
        st.mem.readSized sz sgn (evalAddrMode st addr).1 := by
      rw [hrel.mem_inv.tight_eq]; exact tightenMem_readSized_eq (hrel.mem_inv.tight_eq ▸ hcr_t)
    simp only [hcr_t, hcr_st, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hrd_eq]
    rcases hwb : (evalAddrMode st addr).2 with _ | ⟨base, nb⟩
    · exact stateTightRel_advancePC (stateTightRel_writeReg hrel w _ hallow.2)
    · exact stateTightRel_advancePC
        (stateTightRel_writeReg (stateTightRel_writeReg64 hrel nb (hwb_ok base nb hwb)) w _ hallow.2)
  | ldp w sgn rt1 rt2 addr =>
    dsimp [instrAllowed] at hallow; simp only [Bool.and_eq_true] at hallow
    rcases hallow with ⟨⟨ha, hrt1⟩, hrt2⟩
    obtain ⟨hsp_t, hsp_s, heval_eq, hwb_ok⟩ := evalAddrMode_tight_of_addrOk (fp := fp) (st := st) ha
    rw [← ht_eq] at hsp_t heval_eq
    let ea := (evalAddrMode st addr).1
    cases sgn <;> cases w
    · dsimp only [execInst, execInstWithSvc, execLdp] at hrun_next ⊢
      simp only [hsp_t, hsp_s, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval_eq] at hrun_next ⊢
      have hcr_pair : (st_tight.mem.canRead ea MemWidth.W32.bytes && st_tight.mem.canRead (ea + 4#64) MemWidth.W32.bytes) = true := by
        cases hcr : (st_tight.mem.canRead ea MemWidth.W32.bytes && st_tight.mem.canRead (ea + 4#64) MemWidth.W32.bytes)
        · dsimp only [ea] at hcr; rw [hcr] at hrun_next; simp only [Bool.not_false, ↓reduceIte] at hrun_next; cases hrun_next
        · rfl
      simp only [Bool.and_eq_true] at hcr_pair
      have hcr1 := (tightenMem_canRead_imp (hrel.mem_inv.tight_eq ▸ hcr_pair.1)).1
      have hcr2 := (tightenMem_canRead_imp (hrel.mem_inv.tight_eq ▸ hcr_pair.2)).1
      have hrd1 := tightenMem_readSized_eq (sgn := false) (hrel.mem_inv.tight_eq ▸ hcr_pair.1)
      have hrd2 := tightenMem_readSized_eq (sgn := false) (hrel.mem_inv.tight_eq ▸ hcr_pair.2)
      rw [← hrel.mem_inv.tight_eq] at hrd1 hrd2
      dsimp only [ea] at hcr_pair hcr1 hcr2 hrd1 hrd2
      simp only [hcr_pair.1, hcr_pair.2, hcr1, hcr2, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hrd1, hrd2]
      rcases hwb : (evalAddrMode st addr).2 with _ | ⟨base, nb⟩
      · exact stateTightRel_advancePC (stateTightRel_writeReg (stateTightRel_writeReg hrel _ _ hrt1) _ _ hrt2)
      · exact stateTightRel_advancePC (stateTightRel_writeReg (stateTightRel_writeReg (stateTightRel_writeReg64 hrel nb (hwb_ok base nb hwb)) _ _ hrt1) _ _ hrt2)
    · dsimp only [execInst, execInstWithSvc, execLdp] at hrun_next ⊢
      simp only [hsp_t, hsp_s, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval_eq] at hrun_next ⊢
      have hcr_pair : (st_tight.mem.canRead ea MemWidth.X64.bytes && st_tight.mem.canRead (ea + 8#64) MemWidth.X64.bytes) = true := by
        cases hcr : (st_tight.mem.canRead ea MemWidth.X64.bytes && st_tight.mem.canRead (ea + 8#64) MemWidth.X64.bytes)
        · dsimp only [ea] at hcr; rw [hcr] at hrun_next; simp only [Bool.not_false, ↓reduceIte] at hrun_next; cases hrun_next
        · rfl
      simp only [Bool.and_eq_true] at hcr_pair
      have hcr1 := (tightenMem_canRead_imp (hrel.mem_inv.tight_eq ▸ hcr_pair.1)).1
      have hcr2 := (tightenMem_canRead_imp (hrel.mem_inv.tight_eq ▸ hcr_pair.2)).1
      have hrd1 := tightenMem_readSized_eq (sgn := false) (hrel.mem_inv.tight_eq ▸ hcr_pair.1)
      have hrd2 := tightenMem_readSized_eq (sgn := false) (hrel.mem_inv.tight_eq ▸ hcr_pair.2)
      rw [← hrel.mem_inv.tight_eq] at hrd1 hrd2
      dsimp only [ea] at hcr_pair hcr1 hcr2 hrd1 hrd2
      simp only [hcr_pair.1, hcr_pair.2, hcr1, hcr2, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hrd1, hrd2]
      rcases hwb : (evalAddrMode st addr).2 with _ | ⟨base, nb⟩
      · exact stateTightRel_advancePC (stateTightRel_writeReg (stateTightRel_writeReg hrel _ _ hrt1) _ _ hrt2)
      · exact stateTightRel_advancePC (stateTightRel_writeReg (stateTightRel_writeReg (stateTightRel_writeReg64 hrel nb (hwb_ok base nb hwb)) _ _ hrt1) _ _ hrt2)
    · dsimp only [execInst, execInstWithSvc, execLdp] at hrun_next ⊢
      simp only [hsp_t, hsp_s, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval_eq] at hrun_next ⊢
      have hcr_pair : (st_tight.mem.canRead ea MemWidth.W32.bytes && st_tight.mem.canRead (ea + 4#64) MemWidth.W32.bytes) = true := by
        cases hcr : (st_tight.mem.canRead ea MemWidth.W32.bytes && st_tight.mem.canRead (ea + 4#64) MemWidth.W32.bytes)
        · dsimp only [ea] at hcr; rw [hcr] at hrun_next; simp only [Bool.not_false, ↓reduceIte] at hrun_next; cases hrun_next
        · rfl
      simp only [Bool.and_eq_true] at hcr_pair
      have hcr1 := (tightenMem_canRead_imp (hrel.mem_inv.tight_eq ▸ hcr_pair.1)).1
      have hcr2 := (tightenMem_canRead_imp (hrel.mem_inv.tight_eq ▸ hcr_pair.2)).1
      have hrd1 := tightenMem_readSized_eq (sgn := true) (hrel.mem_inv.tight_eq ▸ hcr_pair.1)
      have hrd2 := tightenMem_readSized_eq (sgn := true) (hrel.mem_inv.tight_eq ▸ hcr_pair.2)
      rw [← hrel.mem_inv.tight_eq] at hrd1 hrd2
      dsimp only [ea] at hcr_pair hcr1 hcr2 hrd1 hrd2
      simp only [hcr_pair.1, hcr_pair.2, hcr1, hcr2, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hrd1, hrd2]
      rcases hwb : (evalAddrMode st addr).2 with _ | ⟨base, nb⟩
      · exact stateTightRel_advancePC (stateTightRel_writeReg (stateTightRel_writeReg hrel _ _ hrt1) _ _ hrt2)
      · exact stateTightRel_advancePC (stateTightRel_writeReg (stateTightRel_writeReg (stateTightRel_writeReg64 hrel nb (hwb_ok base nb hwb)) _ _ hrt1) _ _ hrt2)
    · dsimp only [execInst, execInstWithSvc, execLdp] at hrun_next ⊢
      simp only [hsp_t, hsp_s, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval_eq] at hrun_next ⊢
      have hcr_pair : (st_tight.mem.canRead ea MemWidth.W32.bytes && st_tight.mem.canRead (ea + 4#64) MemWidth.W32.bytes) = true := by
        cases hcr : (st_tight.mem.canRead ea MemWidth.W32.bytes && st_tight.mem.canRead (ea + 4#64) MemWidth.W32.bytes)
        · dsimp only [ea] at hcr; rw [hcr] at hrun_next; simp only [Bool.not_false, ↓reduceIte] at hrun_next; cases hrun_next
        · rfl
      simp only [Bool.and_eq_true] at hcr_pair
      have hcr1 := (tightenMem_canRead_imp (hrel.mem_inv.tight_eq ▸ hcr_pair.1)).1
      have hcr2 := (tightenMem_canRead_imp (hrel.mem_inv.tight_eq ▸ hcr_pair.2)).1
      have hrd1 := tightenMem_readSized_eq (sgn := true) (hrel.mem_inv.tight_eq ▸ hcr_pair.1)
      have hrd2 := tightenMem_readSized_eq (sgn := true) (hrel.mem_inv.tight_eq ▸ hcr_pair.2)
      rw [← hrel.mem_inv.tight_eq] at hrd1 hrd2
      dsimp only [ea] at hcr_pair hcr1 hcr2 hrd1 hrd2
      simp only [hcr_pair.1, hcr_pair.2, hcr1, hcr2, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hrd1, hrd2]
      rcases hwb : (evalAddrMode st addr).2 with _ | ⟨base, nb⟩
      · exact stateTightRel_advancePC (stateTightRel_writeReg (stateTightRel_writeReg hrel _ _ hrt1) _ _ hrt2)
      · exact stateTightRel_advancePC (stateTightRel_writeReg (stateTightRel_writeReg (stateTightRel_writeReg64 hrel nb (hwb_ok base nb hwb)) _ _ hrt1) _ _ hrt2)
  | str sz rt addr =>
    dsimp [instrAllowed] at hallow; simp only [Bool.and_eq_true] at hallow
    obtain ⟨hsp_t, hsp_s, heval_eq, hwb_ok⟩ := evalAddrMode_tight_of_addrOk (fp := fp) (st := st) hallow.1
    rw [← ht_eq] at hsp_t heval_eq
    have hrt_r : st_tight.readReg64 rt = st.readReg64 rt := by rw [ht_eq]; exact readReg64_tight_of_noSp hallow.2
    dsimp only [execInst, execInstWithSvc, execStr] at hrun_next ⊢
    simp only [hsp_t, hsp_s, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval_eq, hrt_r] at hrun_next ⊢
    have hcw_t : st_tight.mem.canWrite (evalAddrMode st addr).1 sz.bytes = true := by
      cases hcw : st_tight.mem.canWrite (evalAddrMode st addr).1 sz.bytes
      · rw [hcw] at hrun_next; cases hrun_next
      · rfl
    have ⟨hcw_st, hfp_ea⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_t)
    simp only [hcw_t, hcw_st, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hmem' := memTightInv_writeSized hrel.mem_inv (st.readReg64 rt) hfp_ea
    rcases hwb : (evalAddrMode st addr).2 with _ | ⟨base, nb⟩
    · simp only [hwb]
      exact stateTightRel_advancePC (stateTightRel_setMem hrel hmem')
    · simp only [hwb]
      exact stateTightRel_advancePC
        (stateTightRel_writeReg64 (stateTightRel_setMem hrel hmem') nb (hwb_ok base nb hwb))
  | stp w rt1 rt2 addr =>
    dsimp [instrAllowed] at hallow; simp only [Bool.and_eq_true] at hallow
    rcases hallow with ⟨⟨ha, hrt1⟩, hrt2⟩
    obtain ⟨hsp_t, hsp_s, heval_eq, hwb_ok⟩ := evalAddrMode_tight_of_addrOk (fp := fp) (st := st) ha
    rw [← ht_eq] at hsp_t heval_eq
    have hrt1_r : st_tight.readReg64 rt1 = st.readReg64 rt1 := by rw [ht_eq]; exact readReg64_tight_of_noSp hrt1
    have hrt2_r : st_tight.readReg64 rt2 = st.readReg64 rt2 := by rw [ht_eq]; exact readReg64_tight_of_noSp hrt2
    let ea := (evalAddrMode st addr).1
    cases w
    · dsimp only [execInst, execInstWithSvc, execStp] at hrun_next ⊢
      simp only [hsp_t, hsp_s, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval_eq, hrt1_r, hrt2_r] at hrun_next ⊢
      have hcw_pair : (st_tight.mem.canWrite ea MemWidth.W32.bytes && st_tight.mem.canWrite (ea + 4#64) MemWidth.W32.bytes) = true := by
        cases hcw : (st_tight.mem.canWrite ea MemWidth.W32.bytes && st_tight.mem.canWrite (ea + 4#64) MemWidth.W32.bytes)
        · dsimp only [ea] at hcw; rw [hcw] at hrun_next; simp only [Bool.not_false, ↓reduceIte] at hrun_next; cases hrun_next
        · rfl
      simp only [Bool.and_eq_true] at hcw_pair
      have ⟨hcw1, hfp1⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_pair.1)
      have ⟨hcw2, hfp2⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_pair.2)
      have hmem1 := memTightInv_writeSized hrel.mem_inv (st.readReg64 rt1) hfp1
      have hmem2 := memTightInv_writeSized hmem1 (st.readReg64 rt2) hfp2
      dsimp only [ea] at hcw_pair hcw1 hcw2 hmem1 hmem2
      simp only [hcw_pair.1, hcw_pair.2, hcw1, hcw2, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rcases hwb : (evalAddrMode st addr).2 with _ | ⟨base, nb⟩
      · simp only [hwb]; exact stateTightRel_advancePC (stateTightRel_setMem hrel hmem2)
      · simp only [hwb]; exact stateTightRel_advancePC (stateTightRel_writeReg64 (stateTightRel_setMem hrel hmem2) nb (hwb_ok base nb hwb))
    · dsimp only [execInst, execInstWithSvc, execStp] at hrun_next ⊢
      simp only [hsp_t, hsp_s, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval_eq, hrt1_r, hrt2_r] at hrun_next ⊢
      have hcw_pair : (st_tight.mem.canWrite ea MemWidth.X64.bytes && st_tight.mem.canWrite (ea + 8#64) MemWidth.X64.bytes) = true := by
        cases hcw : (st_tight.mem.canWrite ea MemWidth.X64.bytes && st_tight.mem.canWrite (ea + 8#64) MemWidth.X64.bytes)
        · dsimp only [ea] at hcw; rw [hcw] at hrun_next; simp only [Bool.not_false, ↓reduceIte] at hrun_next; cases hrun_next
        · rfl
      simp only [Bool.and_eq_true] at hcw_pair
      have ⟨hcw1, hfp1⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_pair.1)
      have ⟨hcw2, hfp2⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_pair.2)
      have hmem1 := memTightInv_writeSized hrel.mem_inv (st.readReg64 rt1) hfp1
      have hmem2 := memTightInv_writeSized hmem1 (st.readReg64 rt2) hfp2
      dsimp only [ea] at hcw_pair hcw1 hcw2 hmem1 hmem2
      simp only [hcw_pair.1, hcw_pair.2, hcw1, hcw2, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rcases hwb : (evalAddrMode st addr).2 with _ | ⟨base, nb⟩
      · simp only [hwb]; exact stateTightRel_advancePC (stateTightRel_setMem hrel hmem2)
      · simp only [hwb]; exact stateTightRel_advancePC (stateTightRel_writeReg64 (stateTightRel_setMem hrel hmem2) nb (hwb_ok base nb hwb))
  | strSimd sz vt addr =>
    dsimp [instrAllowed] at hallow
    obtain ⟨hsp_t, hsp_s, heval_eq, hwb_ok⟩ := evalAddrMode_tight_of_addrOk (fp := fp) (st := st) hallow
    rw [← ht_eq] at hsp_t heval_eq
    have hvt_r : st_tight.readVReg128 vt = st.readVReg128 vt := by rw [ht_eq]; rfl
    dsimp only [execInst, execInstWithSvc] at hrun_next ⊢
    simp only [hsp_t, hsp_s, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval_eq, hvt_r] at hrun_next ⊢
    have hcw_t : st_tight.mem.canWrite (evalAddrMode st addr).1 sz.bytes = true := by
      cases hcw : st_tight.mem.canWrite (evalAddrMode st addr).1 sz.bytes
      · rw [hcw] at hrun_next; cases hrun_next
      · rfl
    have ⟨hcw_st, hfp_ea⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_t)
    simp only [hcw_t, hcw_st, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hmem' := memTightInv_writeSimdSized hrel.mem_inv (st.readVReg128 vt) hfp_ea
    rcases hwb : (evalAddrMode st addr).2 with _ | ⟨base, nb⟩
    · simp only [hwb]
      exact stateTightRel_advancePC (stateTightRel_setMem hrel hmem')
    · simp only [hwb]
      exact stateTightRel_advancePC
        (stateTightRel_writeReg64 (stateTightRel_setMem hrel hmem') nb (hwb_ok base nb hwb))
  | stpSimd sz vt1 vt2 addr =>
    dsimp [instrAllowed] at hallow
    obtain ⟨hsp_t, hsp_s, heval_eq, hwb_ok⟩ := evalAddrMode_tight_of_addrOk (fp := fp) (st := st) hallow
    rw [← ht_eq] at hsp_t heval_eq
    have hvt1_r : st_tight.readVReg128 vt1 = st.readVReg128 vt1 := by rw [ht_eq]; rfl
    have hvt2_r : st_tight.readVReg128 vt2 = st.readVReg128 vt2 := by rw [ht_eq]; rfl
    let ea := (evalAddrMode st addr).1
    cases sz
    · dsimp only [execInst, execInstWithSvc] at hrun_next ⊢
      simp only [hsp_t, hsp_s, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval_eq, hvt1_r, hvt2_r] at hrun_next ⊢
      have hcw_pair : (st_tight.mem.canWrite ea SimdMemSize.B8.bytes && st_tight.mem.canWrite (ea + 1#64) SimdMemSize.B8.bytes) = true := by
        cases hcw : (st_tight.mem.canWrite ea SimdMemSize.B8.bytes && st_tight.mem.canWrite (ea + 1#64) SimdMemSize.B8.bytes)
        · dsimp only [ea] at hcw; rw [hcw] at hrun_next; simp only [Bool.not_false, ↓reduceIte] at hrun_next; cases hrun_next
        · rfl
      simp only [Bool.and_eq_true] at hcw_pair
      have ⟨hcw1, hfp1⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_pair.1)
      have ⟨hcw2, hfp2⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_pair.2)
      have hmem1 := memTightInv_writeSimdSized hrel.mem_inv (st.readVReg128 vt1) hfp1
      have hmem2 := memTightInv_writeSimdSized hmem1 (st.readVReg128 vt2) hfp2
      dsimp only [ea] at hcw_pair hcw1 hcw2 hmem1 hmem2
      simp only [hcw_pair.1, hcw_pair.2, hcw1, hcw2, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rcases hwb : (evalAddrMode st addr).2 with _ | ⟨base, nb⟩
      · simp only [hwb]; exact stateTightRel_advancePC (stateTightRel_setMem hrel hmem2)
      · simp only [hwb]; exact stateTightRel_advancePC (stateTightRel_writeReg64 (stateTightRel_setMem hrel hmem2) nb (hwb_ok base nb hwb))
    · dsimp only [execInst, execInstWithSvc] at hrun_next ⊢
      simp only [hsp_t, hsp_s, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval_eq, hvt1_r, hvt2_r] at hrun_next ⊢
      have hcw_pair : (st_tight.mem.canWrite ea SimdMemSize.H16.bytes && st_tight.mem.canWrite (ea + 2#64) SimdMemSize.H16.bytes) = true := by
        cases hcw : (st_tight.mem.canWrite ea SimdMemSize.H16.bytes && st_tight.mem.canWrite (ea + 2#64) SimdMemSize.H16.bytes)
        · dsimp only [ea] at hcw; rw [hcw] at hrun_next; simp only [Bool.not_false, ↓reduceIte] at hrun_next; cases hrun_next
        · rfl
      simp only [Bool.and_eq_true] at hcw_pair
      have ⟨hcw1, hfp1⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_pair.1)
      have ⟨hcw2, hfp2⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_pair.2)
      have hmem1 := memTightInv_writeSimdSized hrel.mem_inv (st.readVReg128 vt1) hfp1
      have hmem2 := memTightInv_writeSimdSized hmem1 (st.readVReg128 vt2) hfp2
      dsimp only [ea] at hcw_pair hcw1 hcw2 hmem1 hmem2
      simp only [hcw_pair.1, hcw_pair.2, hcw1, hcw2, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rcases hwb : (evalAddrMode st addr).2 with _ | ⟨base, nb⟩
      · simp only [hwb]; exact stateTightRel_advancePC (stateTightRel_setMem hrel hmem2)
      · simp only [hwb]; exact stateTightRel_advancePC (stateTightRel_writeReg64 (stateTightRel_setMem hrel hmem2) nb (hwb_ok base nb hwb))
    · dsimp only [execInst, execInstWithSvc] at hrun_next ⊢
      simp only [hsp_t, hsp_s, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval_eq, hvt1_r, hvt2_r] at hrun_next ⊢
      have hcw_pair : (st_tight.mem.canWrite ea SimdMemSize.S32.bytes && st_tight.mem.canWrite (ea + 4#64) SimdMemSize.S32.bytes) = true := by
        cases hcw : (st_tight.mem.canWrite ea SimdMemSize.S32.bytes && st_tight.mem.canWrite (ea + 4#64) SimdMemSize.S32.bytes)
        · dsimp only [ea] at hcw; rw [hcw] at hrun_next; simp only [Bool.not_false, ↓reduceIte] at hrun_next; cases hrun_next
        · rfl
      simp only [Bool.and_eq_true] at hcw_pair
      have ⟨hcw1, hfp1⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_pair.1)
      have ⟨hcw2, hfp2⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_pair.2)
      have hmem1 := memTightInv_writeSimdSized hrel.mem_inv (st.readVReg128 vt1) hfp1
      have hmem2 := memTightInv_writeSimdSized hmem1 (st.readVReg128 vt2) hfp2
      dsimp only [ea] at hcw_pair hcw1 hcw2 hmem1 hmem2
      simp only [hcw_pair.1, hcw_pair.2, hcw1, hcw2, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rcases hwb : (evalAddrMode st addr).2 with _ | ⟨base, nb⟩
      · simp only [hwb]; exact stateTightRel_advancePC (stateTightRel_setMem hrel hmem2)
      · simp only [hwb]; exact stateTightRel_advancePC (stateTightRel_writeReg64 (stateTightRel_setMem hrel hmem2) nb (hwb_ok base nb hwb))
    · dsimp only [execInst, execInstWithSvc] at hrun_next ⊢
      simp only [hsp_t, hsp_s, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval_eq, hvt1_r, hvt2_r] at hrun_next ⊢
      have hcw_pair : (st_tight.mem.canWrite ea SimdMemSize.D64.bytes && st_tight.mem.canWrite (ea + 8#64) SimdMemSize.D64.bytes) = true := by
        cases hcw : (st_tight.mem.canWrite ea SimdMemSize.D64.bytes && st_tight.mem.canWrite (ea + 8#64) SimdMemSize.D64.bytes)
        · dsimp only [ea] at hcw; rw [hcw] at hrun_next; simp only [Bool.not_false, ↓reduceIte] at hrun_next; cases hrun_next
        · rfl
      simp only [Bool.and_eq_true] at hcw_pair
      have ⟨hcw1, hfp1⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_pair.1)
      have ⟨hcw2, hfp2⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_pair.2)
      have hmem1 := memTightInv_writeSimdSized hrel.mem_inv (st.readVReg128 vt1) hfp1
      have hmem2 := memTightInv_writeSimdSized hmem1 (st.readVReg128 vt2) hfp2
      dsimp only [ea] at hcw_pair hcw1 hcw2 hmem1 hmem2
      simp only [hcw_pair.1, hcw_pair.2, hcw1, hcw2, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rcases hwb : (evalAddrMode st addr).2 with _ | ⟨base, nb⟩
      · simp only [hwb]; exact stateTightRel_advancePC (stateTightRel_setMem hrel hmem2)
      · simp only [hwb]; exact stateTightRel_advancePC (stateTightRel_writeReg64 (stateTightRel_setMem hrel hmem2) nb (hwb_ok base nb hwb))
    · dsimp only [execInst, execInstWithSvc] at hrun_next ⊢
      simp only [hsp_t, hsp_s, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heval_eq, hvt1_r, hvt2_r] at hrun_next ⊢
      have hcw_pair : (st_tight.mem.canWrite ea SimdMemSize.Q128.bytes && st_tight.mem.canWrite (ea + 16#64) SimdMemSize.Q128.bytes) = true := by
        cases hcw : (st_tight.mem.canWrite ea SimdMemSize.Q128.bytes && st_tight.mem.canWrite (ea + 16#64) SimdMemSize.Q128.bytes)
        · dsimp only [ea] at hcw; rw [hcw] at hrun_next; simp only [Bool.not_false, ↓reduceIte] at hrun_next; cases hrun_next
        · rfl
      simp only [Bool.and_eq_true] at hcw_pair
      have ⟨hcw1, hfp1⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_pair.1)
      have ⟨hcw2, hfp2⟩ := tightenMem_canWrite_imp (hrel.mem_inv.tight_eq ▸ hcw_pair.2)
      have hmem1 := memTightInv_writeSimdSized hrel.mem_inv (st.readVReg128 vt1) hfp1
      have hmem2 := memTightInv_writeSimdSized hmem1 (st.readVReg128 vt2) hfp2
      dsimp only [ea] at hcw_pair hcw1 hcw2 hmem1 hmem2
      simp only [hcw_pair.1, hcw_pair.2, hcw1, hcw2, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rcases hwb : (evalAddrMode st addr).2 with _ | ⟨base, nb⟩
      · simp only [hwb]; exact stateTightRel_advancePC (stateTightRel_setMem hrel hmem2)
      · simp only [hwb]; exact stateTightRel_advancePC (stateTightRel_writeReg64 (stateTightRel_setMem hrel hmem2) nb (hwb_ok base nb hwb))
  | simdInsDup q op imm5 imm4 rn rd =>
    dsimp [instrAllowed] at hallow
    cases op
    · simp only [Bool.not_false, Bool.true_and] at hallow
      by_cases hi1 : (imm4 == 0b0001#4) = true
      · simp only [hi1, ↓reduceIte, Bool.and_eq_true] at hallow
        have himm4 : imm4 = 0b0001#4 := of_decide_eq_true hi1
        subst himm4
        have hrn_r : st_tight.readReg64 (Reg.fromZRBits rn) = st.readReg64 (Reg.fromZRBits rn) := by
          rw [ht_eq]; exact readReg64_tight_of_noSp hallow.1
        dsimp only [execInst, execInstWithSvc] at hrun_next ⊢
        cases h0 : (imm5.extractLsb' 0 4 == 0#4)
        · simp only [h0, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and,
            show (0b0001#4 == 0b0001#4) = true from rfl,
            show (0b0001#4 == 0b0000#4) = false from rfl,
            show (0b0001#4 == 0b0011#4) = false from rfl,
            show (0b0001#4 == 0b0111#4) = false from rfl,
            show (0b0001#4 == 0b0101#4) = false from rfl,
            Bool.false_and, Bool.and_false] at hrun_next ⊢
          let esz : Nat :=
            if (imm5.extractLsb' 0 1) == 1#1 then 8
            else if (imm5.extractLsb' 0 2) == 2#2 then 16
            else if (imm5.extractLsb' 0 3) == 4#3 then 32
            else 64
          cases hg : !(esz == 64 && !q)
          · dsimp only [esz] at hg; rw [hg] at hrun_next
            simp only [Bool.false_eq_true, ↓reduceIte] at hrun_next; cases hrun_next
          · dsimp only [esz] at hg
            simp only [hg, ↓reduceIte, hrn_r]
            exact stateTightRel_advancePC (stateTightRel_writeVReg128 hrel _ hallow.2)
        · rw [h0] at hrun_next; cases hrun_next
      · simp only [hi1, Bool.false_eq_true, ↓reduceIte] at hallow
        by_cases hi0 : (imm4 == 0b0000#4) = true
        · simp only [hi0, ↓reduceIte] at hallow
          have himm4 : imm4 = 0b0000#4 := of_decide_eq_true hi0
          subst himm4
          have hvn_r : st_tight.readVReg128 rn = st.readVReg128 rn := by rw [ht_eq]; rfl
          dsimp only [execInst, execInstWithSvc] at hrun_next ⊢
          cases h0 : (imm5.extractLsb' 0 4 == 0#4)
          · simp only [h0, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and,
              show (0b0000#4 == 0b0001#4) = false from rfl,
              show (0b0000#4 == 0b0000#4) = true from rfl,
              show (0b0000#4 == 0b0011#4) = false from rfl,
              show (0b0000#4 == 0b0111#4) = false from rfl,
              show (0b0000#4 == 0b0101#4) = false from rfl,
              Bool.false_and, Bool.and_false] at hrun_next ⊢
            let esz : Nat :=
              if (imm5.extractLsb' 0 1) == 1#1 then 8
              else if (imm5.extractLsb' 0 2) == 2#2 then 16
              else if (imm5.extractLsb' 0 3) == 4#3 then 32
              else 64
            cases hg : !(esz == 64 && !q)
            · dsimp only [esz] at hg; rw [hg] at hrun_next
              simp only [Bool.false_eq_true, ↓reduceIte] at hrun_next; cases hrun_next
            · dsimp only [esz] at hg
              simp only [hg, ↓reduceIte, hvn_r]
              exact stateTightRel_advancePC (stateTightRel_writeVReg128 hrel _ hallow)
          · rw [h0] at hrun_next; cases hrun_next
        · simp only [hi0, Bool.false_eq_true, ↓reduceIte] at hallow
          by_cases hi7 : (imm4 == 0b0111#4) = true
          · simp only [hi7, ↓reduceIte] at hallow
            have himm4 : imm4 = 0b0111#4 := of_decide_eq_true hi7
            subst himm4
            have hvn_r : st_tight.readVReg128 rn = st.readVReg128 rn := by rw [ht_eq]; rfl
            dsimp only [execInst, execInstWithSvc] at hrun_next ⊢
            cases h0 : (imm5.extractLsb' 0 4 == 0#4)
            · simp only [h0, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and,
                show (0b0111#4 == 0b0001#4) = false from rfl,
                show (0b0111#4 == 0b0000#4) = false from rfl,
                show (0b0111#4 == 0b0011#4) = false from rfl,
                show (0b0111#4 == 0b0111#4) = true from rfl,
                show (0b0111#4 == 0b0101#4) = false from rfl,
                Bool.false_and, Bool.and_false] at hrun_next ⊢
              let esz : Nat :=
                if (imm5.extractLsb' 0 1) == 1#1 then 8
                else if (imm5.extractLsb' 0 2) == 2#2 then 16
                else if (imm5.extractLsb' 0 3) == 4#3 then 32
                else 64
              cases hg : ((q && esz == 64) || (!q && decide (esz < 64)))
              · dsimp only [esz] at hg; rw [hg] at hrun_next
                simp only [Bool.false_eq_true, ↓reduceIte] at hrun_next; cases hrun_next
              · dsimp only [esz] at hg
                simp only [hg, ↓reduceIte, hvn_r]
                exact stateTightRel_advancePC (stateTightRel_writeReg hrel _ _ hallow)
            · rw [h0] at hrun_next; cases hrun_next
          · simp only [hi7, Bool.false_eq_true, ↓reduceIte] at hallow
    · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hallow
  | _ => cases hallow

/-- Lift `Steps (pureWordsProg addr words) s0' sf'` (`sf'.status = .Running`, where `s0'` is the
    `stripS` of `{ s0 with sp := 0#64, mem := tightenMem fp s0.mem }`) directly to `Steps P s0 sf`
    on the real state `s0`, establishing `StateTightRel fp gprOk vregOk s0 sf sf_tight`. -/
private theorem steps_lift_tighten_blockExternFree {P : Program}
    {addr : BitVec 64} {words : List (BitVec 32)}
    {fp : BitVec 64 → Bool} {gprOk vregOk : BitVec 5 → Bool}
    (hall : (pureWordsProg addr words).allInstrs
      (fun i => !i.isSvc && !i.isMsrTpidrEl0 && instrAllowed gprOk vregOk i) = true)
    (hext : BlockExternFree P addr (4 * words.length))
    {s0' sf' : State} (hsteps : Steps (pureWordsProg addr words) s0' sf')
    (hrun_f : sf'.status = .Running) :
    ∀ {s0 st st_tight : State},
      StateTightRel fp gprOk vregOk s0 st st_tight →
      s0' = stripS (progKeep (pureWordsProg addr words)) st_tight →
      (pureWordsProg addr words).CodeLoaded st.mem →
      ∃ sf sf_tight : State,
        Steps P st sf ∧
        sf' = stripS (progKeep (pureWordsProg addr words)) sf_tight ∧
        StateTightRel fp gprOk vregOk s0 sf sf_tight := by
  let prog₀ := pureWordsProg addr words
  have hclen : prog₀.code.length = 4 * words.length :=
    Program.length_flatMap_wordToBytesLE words
  induction hsteps with
  | refl _ =>
    intro s0 st st_tight hrel hs0' _
    exact ⟨st, st_tight, Steps.refl st, hs0', hrel⟩
  | @step sa' sb' _ hstep hrest ih =>
    intro s0 st st_tight hrel hsa hLst
    have hLst_tight : prog₀.CodeLoaded st_tight.mem := by
      rw [hrel.mem_inv.tight_eq]; exact tightenMem_codeLoaded hLst
    have hLsa' : prog₀.CodeLoaded sa'.mem := by
      rw [hsa, ss_mem_local]; exact strip_codeLoaded_local hLst_tight
    cases hstep with
    | halt_unmapped _ _ _ =>
      have heq := Steps.from_not_running hrest (by simp)
      subst heq; cases hrun_f
    | extern _ hext0 _ _ | extern_fault _ hext0 _ =>
      simp [pureWordsProg, Program.ofWords, Program.externAt?, Program.hookAtOff?] at hext0
    | @exec inst hrun' hfm' =>
      have hp_i := Program.fetchMem_of_allInstrs hall hLsa'
        (by rw [hsa, ss_mem_local]; exact strip_execOnlyIn_local _ _) sa'.pc inst hfm'
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp_i
      rcases hp_i with ⟨⟨hsvc, _⟩, hallow⟩
      have hsvc0 : inst.isSvc0 = false := inst.isSvc0_eq_false_of_isSvc_eq_false hsvc
      have hpc_eq : st_tight.pc = st.pc := by rw [hrel.tight_eq]
      have hfmP : P.fetchMem st.mem st.pc = some inst := by
        rw [hsa, ss_pc_local, hpc_eq, ss_mem_local] at hfm'
        unfold Program.fetchMem at hfm' ⊢
        have he0 : prog₀.externAt? st.pc = none := rfl
        rw [he0] at hfm'
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
        by_cases hal_pc : st.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
          split at hfm'; · contradiction
          rename_i hce'
          simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
          have hce_all := hce'
          unfold Memory.canExec at hce_all
          rw [Memory.allPerm_iff] at hce_all
          have hx0 : ((stripExecOutside (progKeep prog₀) st_tight.mem).perm (st.pc + BitVec.ofNat 64 0)).x = true :=
            hce_all 0 (by decide)
          have hpc_in_prog : (st.pc - prog₀.base).toNat < prog₀.code.length := by
            have h0 : st.pc + BitVec.ofNat 64 0 = st.pc := by simp
            rw [h0] at hx0
            exact strip_execOnlyIn_local prog₀ st_tight.mem st.pc hx0
          have hpc_in_reg : ProofLib.InRegion addr (4 * words.length) st.pc := by
            dsimp [ProofLib.InRegion]
            change (st.pc - prog₀.base).toNat < 4 * words.length
            rwa [← hclen]
          rw [hext st.pc hpc_in_reg]
          simp only [Option.isSome_none, Bool.false_eq_true, hal_pc, ne_eq, not_true_eq_false, ↓reduceIte]
          have hce_st : st.mem.canExec st.pc 4 = true := by
            unfold Memory.canExec; rw [Memory.allPerm_iff]
            intro k hk
            have hxk := hce_all k hk
            have hin_k : (st.pc + BitVec.ofNat 64 k - prog₀.base).toNat < prog₀.code.length :=
              strip_execOnlyIn_local prog₀ st_tight.mem _ hxk
            have hsub : prog₀.base + BitVec.ofNat 64 ((st.pc + BitVec.ofNat 64 k - prog₀.base).toNat) =
                st.pc + BitVec.ofNat 64 k := by
              rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
            have hp_k := hLst.perm_eq ((st.pc + BitVec.ofNat 64 k - prog₀.base).toNat) hin_k
            rw [hsub] at hp_k; rw [hp_k]; rfl
          have hr32 : (stripExecOutside (progKeep prog₀) st_tight.mem).read32 st.pc = st.mem.read32 st.pc := by
            have hr_byte : ∀ k < 4, (stripExecOutside (progKeep prog₀) st_tight.mem).read8 (st.pc + BitVec.ofNat 64 k) =
                st.mem.read8 (st.pc + BitVec.ofNat 64 k) := by
              intro k hk
              have hxk := hce_all k hk
              have hin_k := strip_execOnlyIn_local prog₀ st_tight.mem _ hxk
              have hsub : prog₀.base + BitVec.ofNat 64 ((st.pc + BitVec.ofNat 64 k - prog₀.base).toNat) =
                  st.pc + BitVec.ofNat 64 k := by
                rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
              rw [strip_read8]
              have hb1 := hLst_tight.byte_eq _ hin_k
              have hb2 := hLst.byte_eq _ hin_k
              rw [hsub] at hb1 hb2
              exact hb1.trans hb2.symm
            have h0 := hr_byte 0 (by decide)
            change (stripExecOutside (progKeep prog₀) st_tight.mem).read8 (st.pc + 0#64) = st.mem.read8 (st.pc + 0#64) at h0
            have h1 := hr_byte 1 (by decide)
            change (stripExecOutside (progKeep prog₀) st_tight.mem).read8 (st.pc + 1#64) = st.mem.read8 (st.pc + 1#64) at h1
            have h2 := hr_byte 2 (by decide)
            change (stripExecOutside (progKeep prog₀) st_tight.mem).read8 (st.pc + 2#64) = st.mem.read8 (st.pc + 2#64) at h2
            have h3 := hr_byte 3 (by decide)
            change (stripExecOutside (progKeep prog₀) st_tight.mem).read8 (st.pc + 3#64) = st.mem.read8 (st.pc + 3#64) at h3
            simp only [Memory.read32, h0, h1, h2, h3]
          rw [hr32] at hfm'
          simp only [hce_st, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact hfm'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfm'; contradiction
      let st2 := P.evalInst inst st
      have hstepP : Step P st st2 := Step.exec hrel.run_st hfmP
      have hst2_eq : st2 = execInst inst st := evalInst_eq_execInst_of_not_isSvc0 hsvc0 st
      have hsb_eq : prog₀.evalInst inst sa' = stripS (progKeep prog₀) (execInst inst st_tight) := by
        rw [evalInst_eq_execInst_of_not_isSvc0 hsvc0, hsa, execInst_stripS hsvc0]
      have hrun_sb' : (prog₀.evalInst inst sa').status = .Running := by
        refine Classical.byContradiction fun hnr => ?_
        have heq := Steps.from_not_running hrest hnr
        rw [heq] at hrun_f; exact hnr hrun_f
      have hrun_next_tight : (execInst inst st_tight).status = .Running := by
        rw [hsb_eq] at hrun_sb'
        cases he : execInst inst st_tight
        rw [he] at hrun_sb'; exact hrun_sb'
      have hrel2 : StateTightRel fp gprOk vregOk s0 st2 (execInst inst st_tight) :=
        hst2_eq ▸ execInst_stateTightRel_step hrel hallow hrun_next_tight
      obtain ⟨sf, sf_tight, hrestP, hsf', hrel_f⟩ := ih hrun_f hrel2 hsb_eq (hstepP.codeLoaded hLst)
      exact ⟨sf, sf_tight, Steps.step hstepP hrestP, hsf', hrel_f⟩

/-! ### 6c. Memory & State Reconstruction Helpers (`sf = apply*Clobber ...`) -/

private theorem cell_eq_of_rw_noLazy {m1 m2 : Memory} {a : BitVec 64}
    (hp1 : m1.perm a = some Perm.rw) (hp2 : m2.perm a = some Perm.rw)
    (hlf1 : m1.isLazyFree a = false) (hlf2 : m2.isLazyFree a = false)
    (han : m1.isAnon a = m2.isAnon a) (hr : m1.read8 a = m2.read8 a) :
    m1.cells a = m2.cells a := by
  dsimp only [Memory.perm, Memory.isLazyFree, Memory.isAnon, Memory.read8, Perm.rwx, Perm.rw] at hp1 hp2 hlf1 hlf2 han hr
  revert hp1 hlf1 han hr
  rcases m1.cells a with _ | ⟨_ | ⟨r1, w1, x1, lf1, an1⟩, b1⟩ <;> intro hp1 hlf1 han hr
  · cases hp1
  · cases hp1
  · revert hp2 hlf2 han hr
    rcases m2.cells a with _ | ⟨_ | ⟨r2, w2, x2, lf2, an2⟩, b2⟩ <;> intro hp2 hlf2 han hr
    · cases hp2
    · cases hp2
    · simp only [Option.some.injEq, Perm.mk.injEq, Prod.mk.injEq] at hp1 hp2 hlf1 hlf2 han hr ⊢
      exact ⟨⟨hp1.1.trans hp2.1.symm, hp1.2.1.trans hp2.2.1.symm, hp1.2.2.1.trans hp2.2.2.1.symm,
        hlf1.trans hlf2.symm, han⟩, hr⟩

private theorem writeBytes_cells_outside {m : Memory} {base : BitVec 64} {bs : List (BitVec 8)}
    {a : BitVec 64} (hlen : bs.length ≤ 2 ^ 64) (hout : ¬ InRegion base bs.length a) :
    (m.writeBytes base bs).cells a = m.cells a := by
  induction bs generalizing m base with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons] at hlen hout
    have hne : a ≠ base := by
      intro heq; subst heq
      apply hout; simp [InRegion]
    have hout' : ¬ InRegion (base + 1#64) rest.length a := by
      intro hin
      apply hout
      dsimp [InRegion] at hin ⊢
      bv_omega
    dsimp [Memory.writeBytes]
    rw [ih (by omega) hout']
    dsimp [Memory.write8]; simp only [hne, ↓reduceIte]

private theorem writeBytes_perm_eq (m : Memory) (base : BitVec 64) (bs : List (BitVec 8)) :
    (m.writeBytes base bs).perm = m.perm := by
  induction bs generalizing m base with
  | nil => rfl
  | cons b rest ih =>
    dsimp [Memory.writeBytes]; rw [ih]
    funext a
    dsimp [Memory.write8, Memory.perm, Memory.rawPerm, Perm.rwx]
    by_cases ha : a = base
    · subst ha; simp only [↓reduceIte]; rcases m.cells a with _ | ⟨_ | p, byte⟩ <;> rfl
    · simp only [ha, ↓reduceIte]

private theorem writeBytes_isAnon_eq (m : Memory) (base : BitVec 64) (bs : List (BitVec 8)) :
    (m.writeBytes base bs).isAnon = m.isAnon := by
  induction bs generalizing m base with
  | nil => rfl
  | cons b rest ih =>
    dsimp [Memory.writeBytes]; rw [ih]
    funext a
    dsimp [Memory.write8, Memory.isAnon, Memory.rawPerm]
    by_cases ha : a = base
    · subst ha; simp only [↓reduceIte]; rcases m.cells a with _ | ⟨_ | p, byte⟩ <;> rfl
    · simp only [ha, ↓reduceIte]

private theorem writeBytes_isLazyFree_false_imp {m : Memory} (base : BitVec 64) (bs : List (BitVec 8))
    {a : BitVec 64} (hlf : m.isLazyFree a = false) :
    (m.writeBytes base bs).isLazyFree a = false := by
  induction bs generalizing m base with
  | nil => exact hlf
  | cons b rest ih =>
    dsimp [Memory.writeBytes]; apply ih
    dsimp [Memory.write8, Memory.isLazyFree, Memory.rawPerm]
    by_cases ha : a = base
    · subst ha; simp only [↓reduceIte]; rcases m.cells a with _ | ⟨_ | p, byte⟩ <;> rfl
    · simp only [ha, ↓reduceIte]; exact hlf

private theorem readBytes_getElem?_eq (m : Memory) (base : BitVec 64) :
    ∀ (n k : Nat), k < n → (m.readBytes base n)[k]? = some (m.read8 (base + BitVec.ofNat 64 k))
  | 0, _, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, 0, _ => by simp [Memory.readBytes]
  | n + 1, k + 1, hk => by
    simp only [Memory.readBytes, List.getElem?_cons_succ]
    rw [readBytes_getElem?_eq m (base + 1#64) n k (Nat.lt_of_succ_lt_succ hk)]
    congr 2
    rw [BitVec.add_assoc]; congr 1
    change 1#64 + BitVec.ofNat 64 k = BitVec.ofNat 64 (k + 1)
    bv_omega

private theorem writeBytes_read8_in {m : Memory} {base : BitVec 64} {bs : List (BitVec 8)}
    (hlen : bs.length ≤ 2 ^ 64) :
    ∀ (k : Nat) (hk : k < bs.length),
      (m.writeBytes base bs).read8 (base + BitVec.ofNat 64 k) = bs[k]'hk := by
  induction bs generalizing m base with
  | nil => intro _ hk; exact absurd hk (Nat.not_lt_zero _)
  | cons b rest ih =>
    simp only [List.length_cons] at hlen
    intro k hk
    cases k with
    | zero =>
      have hz : base + BitVec.ofNat 64 0 = base := by simp
      rw [hz]
      simp only [List.getElem_cons_zero]
      dsimp [Memory.writeBytes]
      have hout : ¬ InRegion (base + 1#64) rest.length base := by
        dsimp [InRegion]; bv_omega
      have hc := writeBytes_cells_outside (m := m.write8 base b) (by omega) hout
      dsimp [Memory.read8]; rw [hc]
      dsimp [Memory.write8]; simp only [↓reduceIte]
    | succ k' =>
      simp only [List.getElem_cons_succ]
      dsimp [Memory.writeBytes]
      have he : base + BitVec.ofNat 64 (k' + 1) = (base + 1#64) + BitVec.ofNat 64 k' := by
        rw [BitVec.add_assoc]; congr 1
        change BitVec.ofNat 64 (k' + 1) = 1#64 + BitVec.ofNat 64 k'
        bv_omega
      rw [he]
      exact ih (by omega) k' (Nat.lt_of_succ_lt_succ hk)

private theorem mem_eq_writeBytes_of_tight_post {gprOk vregOk : BitVec 5 → Bool}
    {s0 sf sf_tight sf' : State}
    {dst : BitVec 64} {outBytes : List (BitVec 8)}
    (hrw : s0.mem.RW dst outBytes.length)
    (hlen : outBytes.length ≤ 2 ^ 64)
    (hrel : StateTightRel (fun a => decide (InRegion dst outBytes.length a)) gprOk vregOk s0 sf sf_tight)
    (hsf' : sf'.mem.readBytes dst outBytes.length = outBytes)
    (hsf'_read : ∀ a, sf'.mem.read8 a = sf_tight.mem.read8 a) :
    sf.mem = s0.mem.writeBytes dst outBytes := by
  let fp := fun a => decide (InRegion dst outBytes.length a)
  apply Memory.ext; funext a
  by_cases hin : InRegion dst outBytes.length a
  · have hfp : fp a = true := decide_eq_true hin
    obtain ⟨hperm0, hlf0⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hin)
    have hperm_sf : sf.mem.perm a = some Perm.rw := (congrFun hrel.mem_inv.perm_eq a).trans hperm0
    have hperm_wb : (s0.mem.writeBytes dst outBytes).perm a = some Perm.rw :=
      (congrFun (writeBytes_perm_eq s0.mem dst outBytes) a).trans hperm0
    have hlf_sf : sf.mem.isLazyFree a = false := hrel.mem_inv.lf_imp a hlf0
    have hlf_wb : (s0.mem.writeBytes dst outBytes).isLazyFree a = false :=
      writeBytes_isLazyFree_false_imp dst outBytes hlf0
    have han_eq : sf.mem.isAnon a = (s0.mem.writeBytes dst outBytes).isAnon a :=
      (congrFun hrel.mem_inv.anon_eq a).trans (congrFun (writeBytes_isAnon_eq s0.mem dst outBytes) a).symm
    let k := (a - dst).toNat
    have hk : k < outBytes.length := hin
    have ha_eq : dst + BitVec.ofNat 64 k = a := by
      change dst + BitVec.ofNat 64 (a - dst).toNat = a
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have hr_sf' : sf'.mem.read8 a = outBytes[k]'hk := by
      have hget := readBytes_getElem?_eq sf'.mem dst outBytes.length k hk
      rw [hsf', List.getElem?_eq_getElem hk, ha_eq] at hget
      exact (Option.some.inj hget).symm
    have hr_sf : sf.mem.read8 a = outBytes[k]'hk := by
      have h1 : sf'.mem.read8 a = sf.mem.read8 a := by
        rw [hsf'_read a, hrel.mem_inv.tight_eq, tightenMem_read8_in hfp]
      exact h1.symm.trans hr_sf'
    have hr_wb : (s0.mem.writeBytes dst outBytes).read8 a = outBytes[k]'hk := by
      rw [← ha_eq]; exact writeBytes_read8_in hlen k hk
    exact cell_eq_of_rw_noLazy hperm_sf hperm_wb hlf_sf hlf_wb han_eq (hr_sf.trans hr_wb.symm)
  · have hfp : fp a = false := decide_eq_false hin
    rw [hrel.mem_inv.outside_eq a hfp, writeBytes_cells_outside hlen hin]

private theorem state_eq_applyMemcpyClobber {fp : BitVec 64 → Bool}
    {s0 sf sf_tight : State} {m' : Memory} {pc' : BitVec 64}
    (hrun0 : s0.status = .Running)
    (hrel : StateTightRel fp memcpyGprOk (fun _ => false) s0 sf sf_tight)
    (hmem : sf.mem = m') (hpc : sf.pc = pc') :
    sf = applyMemcpyClobber s0 m' pc' (MemcpyClobber.ofState sf) := by
  rcases hrel with ⟨_, hrun, hsp, hregs, hvregs, _, hsys⟩
  have hst : sf.status = s0.status := hrun.trans hrun0.symm
  dsimp [sysProj] at hsys
  simp only [Prod.mk.injEq] at hsys
  rcases hsys with ⟨htp, hfp_sr, hbrkS, hbrk, hfs, hor, horI, hexcl, htr, hsym, hsigA, hsigS, hpma⟩
  cases sf; cases s0
  dsimp only [applyMemcpyClobber, MemcpyClobber.ofState, State.writeReg64, State.setPState,
    State.setMem, State.setPC] at *
  simp only [State.mk.injEq, RegFile.ext_iff, VRegFile.ext_iff]
  refine ⟨funext fun idx => ?_, funext fun idx => hvregs idx rfl,
    hsp, hpc, trivial, hmem, htp, hfp_sr, hbrkS, hbrk, hfs, hor, horI, hexcl, htr, hst, hsym, hsigA, hsigS, hpma⟩
  dsimp only [RegFile.write]
  have hlt : idx.toNat < 32 := idx.isLt
  by_cases h1 : idx = 17#5; · subst h1; rfl
  by_cases h2 : idx = 16#5; · subst h2; simp [h1]
  by_cases h3 : idx = 15#5; · subst h3; simp [h1, h2]
  by_cases h4 : idx = 14#5; · subst h4; simp [h1, h2, h3]
  by_cases h5 : idx = 13#5; · subst h5; simp [h1, h2, h3, h4]
  by_cases h6 : idx = 12#5; · subst h6; simp [h1, h2, h3, h4, h5]
  by_cases h7 : idx = 11#5; · subst h7; simp [h1, h2, h3, h4, h5, h6]
  by_cases h8 : idx = 10#5; · subst h8; simp [h1, h2, h3, h4, h5, h6, h7]
  by_cases h9 : idx = 9#5; · subst h9; simp [h1, h2, h3, h4, h5, h6, h7, h8]
  by_cases h10 : idx = 8#5; · subst h10; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]
  by_cases h11 : idx = 7#5; · subst h11; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  by_cases h12 : idx = 6#5; · subst h12; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  by_cases h13 : idx = 5#5; · subst h13; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  by_cases h14 : idx = 4#5; · subst h14; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  by_cases h15 : idx = 3#5; · subst h15; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  by_cases h16 : idx = 2#5; · subst h16; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  by_cases h17 : idx = 1#5; · subst h17; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  have hgpr : memcpyGprOk idx = false := by
    dsimp [memcpyGprOk]; apply decide_eq_false
    intro ⟨hlo, hhi⟩
    have : idx.toNat = 1 ∨ idx.toNat = 2 ∨ idx.toNat = 3 ∨ idx.toNat = 4 ∨ idx.toNat = 5 ∨
      idx.toNat = 6 ∨ idx.toNat = 7 ∨ idx.toNat = 8 ∨ idx.toNat = 9 ∨ idx.toNat = 10 ∨
      idx.toNat = 11 ∨ idx.toNat = 12 ∨ idx.toNat = 13 ∨ idx.toNat = 14 ∨ idx.toNat = 15 ∨
      idx.toNat = 16 ∨ idx.toNat = 17 := by omega
    rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact h17 (BitVec.eq_of_toNat_eq h)
    · exact h16 (BitVec.eq_of_toNat_eq h)
    · exact h15 (BitVec.eq_of_toNat_eq h)
    · exact h14 (BitVec.eq_of_toNat_eq h)
    · exact h13 (BitVec.eq_of_toNat_eq h)
    · exact h12 (BitVec.eq_of_toNat_eq h)
    · exact h11 (BitVec.eq_of_toNat_eq h)
    · exact h10 (BitVec.eq_of_toNat_eq h)
    · exact h9 (BitVec.eq_of_toNat_eq h)
    · exact h8 (BitVec.eq_of_toNat_eq h)
    · exact h7 (BitVec.eq_of_toNat_eq h)
    · exact h6 (BitVec.eq_of_toNat_eq h)
    · exact h5 (BitVec.eq_of_toNat_eq h)
    · exact h4 (BitVec.eq_of_toNat_eq h)
    · exact h3 (BitVec.eq_of_toNat_eq h)
    · exact h2 (BitVec.eq_of_toNat_eq h)
    · exact h1 (BitVec.eq_of_toNat_eq h)
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, hregs idx hgpr]

private theorem state_eq_applyMemsetClobber {fp : BitVec 64 → Bool}
    {s0 sf sf_tight : State} {m' : Memory} {pc' : BitVec 64}
    (hrun0 : s0.status = .Running)
    (hrel : StateTightRel fp memsetGprOk memsetVRegOk s0 sf sf_tight)
    (hmem : sf.mem = m') (hpc : sf.pc = pc') :
    sf = applyMemsetClobber s0 m' pc' (MemsetClobber.ofState sf) := by
  rcases hrel with ⟨_, hrun, hsp, hregs, hvregs, _, hsys⟩
  have hst : sf.status = s0.status := hrun.trans hrun0.symm
  dsimp [sysProj] at hsys
  simp only [Prod.mk.injEq] at hsys
  rcases hsys with ⟨htp, hfp_sr, hbrkS, hbrk, hfs, hor, horI, hexcl, htr, hsym, hsigA, hsigS, hpma⟩
  cases sf; cases s0
  dsimp only [applyMemsetClobber, MemsetClobber.ofState, State.writeReg64, State.writeVReg128,
    State.setPState, State.setMem, State.setPC] at *
  simp only [State.mk.injEq, RegFile.ext_iff, VRegFile.ext_iff]
  refine ⟨funext fun idx => ?_, funext fun idx => ?_,
    hsp, hpc, trivial, hmem, htp, hfp_sr, hbrkS, hbrk, hfs, hor, horI, hexcl, htr, hst, hsym, hsigA, hsigS, hpma⟩
  · dsimp only [RegFile.write]
    have hlt : idx.toNat < 32 := idx.isLt
    by_cases h1 : idx = 5#5; · subst h1; rfl
    by_cases h2 : idx = 4#5; · subst h2; simp [h1]
    by_cases h3 : idx = 3#5; · subst h3; simp [h1, h2]
    by_cases h4 : idx = 2#5; · subst h4; simp [h1, h2, h3]
    by_cases h5 : idx = 1#5; · subst h5; simp [h1, h2, h3, h4]
    have hgpr : memsetGprOk idx = false := by
      dsimp [memsetGprOk]; apply decide_eq_false
      intro ⟨hlo, hhi⟩
      have : idx.toNat = 1 ∨ idx.toNat = 2 ∨ idx.toNat = 3 ∨ idx.toNat = 4 ∨ idx.toNat = 5 := by omega
      rcases this with h | h | h | h | h
      · exact h5 (BitVec.eq_of_toNat_eq h)
      · exact h4 (BitVec.eq_of_toNat_eq h)
      · exact h3 (BitVec.eq_of_toNat_eq h)
      · exact h2 (BitVec.eq_of_toNat_eq h)
      · exact h1 (BitVec.eq_of_toNat_eq h)
    simp [h1, h2, h3, h4, h5, hregs idx hgpr]
  · dsimp only [VRegFile.write]
    by_cases hv : idx = 0#5
    · subst hv; rfl
    · have hv_ok : memsetVRegOk idx = false := by simp [memsetVRegOk, hv]
      simp [hv, hvregs idx hv_ok]

/-! ## 7. Register-Exact Raw-State `Steps` Theorems (`blk20` `memcpy` & `blk21` `memset`) -/

/-- Register-exact raw-state `Steps` theorem for `memcpySymWords` (`396` B = `99` words) at `addr`
    in **any** `P : Program` satisfying `BlockExternFree P addr 396`:
    - does **not** require `s.spAligned` (`sp` is never accessed);
    - updates **only** `{x1..x17, pstate}`, `mem := s.mem.writeBytes dst bs`, and `pc := lr`,
      preserving `x0`, `x18..x30`, `sp`, `v0..v31`, and all process/system fields (`sysProj`). -/
theorem pureWords_memcpy_steps_exact {P : Program} {addr : BitVec 64} {s : State}
    {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hcl : (pureWordsProg addr memcpySymWords).CodeLoaded s.mem)
    (hext : BlockExternFree P addr 396)
    (hrun : s.status = .Running)
    (hpc : s.pc = addr)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hread : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (hreadable : s.mem.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len) :
    ∃ c : MemcpyClobber,
      Steps P s (applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c) := by
  have hbs_len : bs.length = len := by rw [← hread, Memory.readBytes_length]
  subst hbs_len
  have hlen_lt : bs.length < 2 ^ 64 := by rw [← hx2]; exact (s.readReg64 .x2).isLt
  have hx2_eq : s.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt]
  let fp := fun a => decide (InRegion dst bs.length a)
  let s_tight : State := { s with sp := 0#64, mem := tightenMem fp s.mem }
  let prog₀ := pureWordsProg addr memcpySymWords
  let kp₀ := progKeep prog₀
  have hsat_tight : s_tight.mem ⊨ (memRegion dst bs.length ∗ (src ↦ᵣ bs)) ∗ emp := by
    rw [sepConj_emp]
    exact satisfies_memcpyRO_tight hrw hreadable hdisj hread hlen_lt
  obtain ⟨R_view, hpre_strip, _⟩ := strip_frame kp₀ hsat_tight
  let s0' := stripS kp₀ s_tight
  have hpre' : s0'.mem ⊨ memcpyROSymSpec.pre (dst, src, BitVec.ofNat 64 bs.length, bs) s0' ∗ R_view := by
    have hx0' : s0'.readReg64 .x0 = dst := (ss_r64_local kp₀ s_tight .x0).trans hx0
    have hx1' : s0'.readReg64 .x1 = src := (ss_r64_local kp₀ s_tight .x1).trans hx1
    have hx2' : s0'.readReg64 .x2 = BitVec.ofNat 64 bs.length :=
      (ss_r64_local kp₀ s_tight .x2).trans hx2_eq
    simp only [memcpyROSymSpec, CType.MutSlice8, CType.Bytes, CType.SliceLen,
      CType.SemType.valWf, sepConj_assoc, satisfies_pure_sepConj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlen_lt]
    have hmem_s0' : s0'.mem = stripExecOutside kp₀ s_tight.mem := ss_mem_local kp₀ s_tight
    rw [hmem_s0']
    exact ⟨⟨hx0', hx1', hx2', trivial, trivial⟩, by simpa only [sepConj_assoc] using hpre_strip⟩
  have hsub := memcpyRO_codeAt_ok_sym _ addr (pureWordsProg_memcpy_hasWords_local addr)
  have hsp_al : s0'.spAligned = true := show (0#64 &&& 15#64 == 0#64) = true from by decide
  obtain ⟨sf', hsteps', hout', -⟩ :=
    hsub.no_fault_before_outcome (dst, src, BitVec.ofNat 64 bs.length, bs) R_view s0'
      ((ss_pc_local kp₀ s_tight).trans hpc)
      hrun hpre' hsp_al
      (by rw [ss_mem_local]; exact strip_codeLoaded_local (tightenMem_codeLoaded hcl))
  rcases hout' with ⟨⟨hr_pc, _, hr_st⟩, _, hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · have hext' : BlockExternFree P addr (4 * memcpySymWords.length) := by
      have hl : 4 * memcpySymWords.length = 396 := by decide
      rwa [hl]
    obtain ⟨sf, sf_tight, hstepsP, hsf_eq, hrel⟩ :=
      steps_lift_tighten_blockExternFree (memcpySymWords_allInstrs_allowed addr) hext'
        hsteps' hr_st (stateTightRel_refl fp memcpyGprOk (fun _ => false) s hrun) rfl hcl
    have hpost_bytes : sf'.mem.readBytes dst bs.length = bs := by
      simp only [memcpyROSymSpec, CType.MutSlice8, CType.Bytes, sepConj_assoc] at hpost'
      have hdrop := Satisfies.of_sep_right hpost'
      exact ((IsBlock.pointsToBytes dst bs).read hdrop).2
    have hsf'_read : ∀ a, sf'.mem.read8 a = sf_tight.mem.read8 a := by
      intro a; rw [hsf_eq, ss_mem_local, strip_read8]
    have hmem_sf : sf.mem = s.mem.writeBytes dst bs :=
      mem_eq_writeBytes_of_tight_post hrw (Nat.le_of_lt hlen_lt) hrel hpost_bytes hsf'_read
    have hpc_sf : sf.pc = lr := by
      rw [hsf_eq, ss_pc_local, hrel.tight_eq] at hr_pc
      exact hr_pc.trans ((ss_r64_local kp₀ s_tight .lr).trans hlr)
    refine ⟨MemcpyClobber.ofState sf, ?_⟩
    rwa [← state_eq_applyMemcpyClobber hrun hrel hmem_sf hpc_sf]
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- Register-exact raw-state `Steps` theorem for `VerifiedLibraries.mallocngLib` block `20`
    (`memcpy`, `396` B) on any `P : Program` with `BlockExternFree P (mmpl.base 20) 396`. -/
theorem mallocngBlock20_memcpy_steps_exact {P : Program} {mmpl : Obj.MultiPlacement} {s : State}
    {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hpl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hcl : (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded s.mem)
    (hext : BlockExternFree P (mmpl.base 20) 396)
    (hrun : s.status = .Running)
    (hpc : s.pc = mmpl.base 20)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hread : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (hreadable : s.mem.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len) :
    ∃ c : MemcpyClobber,
      Steps P s (applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c) :=
  pureWords_memcpy_steps_exact
    (codeLoaded_pureWordsProg_of_hasWords hcl
      (mallocngBlock20_hasWords_memcpy_local hpl Syscall.standard) (by decide))
    hext hrun hpc hx0 hx1 hx2 hlr hread hrw hreadable hdisj

/-- Register-exact raw-state `Steps` theorem for `memsetWordsSym` (`260` B = `65` words) at `addr`
    in **any** `P : Program` satisfying `BlockExternFree P addr 260`:
    - does **not** require `s.spAligned` (`sp` is never accessed);
    - updates **only** exact `{x1..x5, v0, pstate}` (`x6..x8` are preserved, NOT clobbered),
      `mem := s.mem.writeBytes dst (List.replicate len val)`, and `pc := lr`,
      preserving `x0`, `x6..x30`, `sp`, `v1..v31`, and all process/system fields (`sysProj`). -/
theorem pureWords_memset_steps_exact {P : Program} {addr : BitVec 64} {s : State}
    {dst lr : BitVec 64} {val : BitVec 8} {len : Nat}
    (hcl : (pureWordsProg addr memsetWordsSym).CodeLoaded s.mem)
    (hext : BlockExternFree P addr 260)
    (hrun : s.status = .Running)
    (hpc : s.pc = addr)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hrw : s.mem.RW dst len) :
    ∃ c : MemsetClobber,
      Steps P s (applyMemsetClobber s (s.mem.writeBytes dst (List.replicate len val)) lr c) := by
  have hlen_lt : len < 2 ^ 64 := by rw [← hx2]; exact (s.readReg64 .x2).isLt
  have hx2_eq : s.readReg64 .x2 = BitVec.ofNat 64 len := by
    apply BitVec.eq_of_toNat_eq
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt]
  have hx1_32 : (s.readReg32 .x1).truncate 8 = val := by
    have htr : ((s.readReg64 .x1).truncate 32).truncate 8 = (s.readReg64 .x1).truncate 8 := by
      bv_bits
    exact htr.trans hx1
  let fp := fun a => decide (InRegion dst len a)
  let s_tight : State := { s with sp := 0#64, mem := tightenMem fp s.mem }
  let prog₀ := pureWordsProg addr memsetWordsSym
  let kp₀ := progKeep prog₀
  have hsat_tight : s_tight.mem ⊨ memRegion dst len ∗ emp := by
    rw [sepConj_emp]
    exact satisfies_memRegion_tight hrw
  obtain ⟨R_view, hpre_strip, _⟩ := strip_frame kp₀ hsat_tight
  let s0' := stripS kp₀ s_tight
  have hpre' : s0'.mem ⊨ memsetSymSpec.pre (dst, s.readReg32 .x1, BitVec.ofNat 64 len) s0' ∗ R_view := by
    have hx0' : s0'.readReg64 .x0 = dst := (ss_r64_local kp₀ s_tight .x0).trans hx0
    have hx1' : s0'.readReg32 .x1 = s.readReg32 .x1 := by
      dsimp [State.readReg32]; rw [ss_r64_local kp₀ s_tight .x1]; rfl
    have hx2' : s0'.readReg64 .x2 = BitVec.ofNat 64 len :=
      (ss_r64_local kp₀ s_tight .x2).trans hx2_eq
    simp only [memsetSymSpec, CType.MutSlice8, CType.Bytes, CType.U32, CType.SizeT,
      CType.scalarTy, CType.SemType.valWf, sepConj_assoc, satisfies_pure_sepConj,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt]
    have hmem_s0' : s0'.mem = stripExecOutside kp₀ s_tight.mem := ss_mem_local kp₀ s_tight
    rw [hmem_s0']
    exact ⟨⟨hx0', hx1', hx2', trivial, trivial⟩, hpre_strip⟩
  have hsub := memset_codeAt_ok_sym _ addr (pureWordsProg_memset_hasWords_local addr)
  have hsp_al : s0'.spAligned = true := show (0#64 &&& 15#64 == 0#64) = true from by decide
  obtain ⟨sf', hsteps', hout', -⟩ :=
    hsub.no_fault_before_outcome (dst, s.readReg32 .x1, BitVec.ofNat 64 len) R_view s0'
      ((ss_pc_local kp₀ s_tight).trans hpc)
      hrun hpre' hsp_al
      (by rw [ss_mem_local]; exact strip_codeLoaded_local (tightenMem_codeLoaded hcl))
  rcases hout' with ⟨⟨hr_pc, _, hr_st⟩, _, hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · have hext' : BlockExternFree P addr (4 * memsetWordsSym.length) := by
      have hl : 4 * memsetWordsSym.length = 260 := by decide
      rwa [hl]
    obtain ⟨sf, sf_tight, hstepsP, hsf_eq, hrel⟩ :=
      steps_lift_tighten_blockExternFree (memsetWordsSym_allInstrs_allowed addr) hext'
        hsteps' hr_st (stateTightRel_refl fp memsetGprOk memsetVRegOk s hrun) rfl hcl
    let outBytes := List.replicate len val
    have hout_len : outBytes.length = len := List.length_replicate
    have hpost_bytes : sf'.mem.readBytes dst outBytes.length = outBytes := by
      simp only [memsetSymSpec, CType.MutSlice8, CType.Bytes, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlen_lt, hx1_32, sepConj_assoc] at hpost'
      have hdrop := Satisfies.of_sep_right hpost'
      exact ((IsBlock.pointsToBytes dst outBytes).read hdrop).2
    have hsf'_read : ∀ a, sf'.mem.read8 a = sf_tight.mem.read8 a := by
      intro a; rw [hsf_eq, ss_mem_local, strip_read8]
    have hrw_out : s.mem.RW dst outBytes.length := hout_len ▸ hrw
    have hrel_out : StateTightRel (fun a => decide (InRegion dst outBytes.length a))
        memsetGprOk memsetVRegOk s sf sf_tight := by
      simpa only [hout_len] using hrel
    have hmem_sf : sf.mem = s.mem.writeBytes dst outBytes :=
      mem_eq_writeBytes_of_tight_post hrw_out (by omega) hrel_out hpost_bytes hsf'_read
    have hpc_sf : sf.pc = lr := by
      rw [hsf_eq, ss_pc_local, hrel.tight_eq] at hr_pc
      exact hr_pc.trans ((ss_r64_local kp₀ s_tight .lr).trans hlr)
    refine ⟨MemsetClobber.ofState sf, ?_⟩
    rwa [← state_eq_applyMemsetClobber hrun hrel hmem_sf hpc_sf]
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- Register-exact raw-state `Steps` theorem for `VerifiedLibraries.mallocngLib` block `21`
    (`memset`, `260` B, exact clobber `{x1..x5, v0, pstate}`) on any `P : Program` with
    `BlockExternFree P (mmpl.base 21) 260`. -/
theorem mallocngBlock21_memset_steps_exact {P : Program} {mmpl : Obj.MultiPlacement} {s : State}
    {dst lr : BitVec 64} {val : BitVec 8} {len : Nat}
    (hpl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hcl : (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded s.mem)
    (hext : BlockExternFree P (mmpl.base 21) 260)
    (hrun : s.status = .Running)
    (hpc : s.pc = mmpl.base 21)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hrw : s.mem.RW dst len) :
    ∃ c : MemsetClobber,
      Steps P s (applyMemsetClobber s (s.mem.writeBytes dst (List.replicate len val)) lr c) :=
  pureWords_memset_steps_exact
    (codeLoaded_pureWordsProg_of_hasWords hcl
      (mallocngBlock21_hasWords_memset_local hpl Syscall.standard) (by decide))
    hext hrun hpc hx0 hx1 hx2 hlr hrw

end LibsignalBinary.Heap.MuslMemOpsRunsTo

