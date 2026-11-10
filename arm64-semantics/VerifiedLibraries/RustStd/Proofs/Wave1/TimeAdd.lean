/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec.TimeAdd
public import VerifiedLibraries.RustStd.Proofs.Wave1.TimePlacement
public import VerifiedLibraries.RustStd.Proofs.Wave1.TimeAddLemmas
public import VerifiedLibraries.RustStd.Proofs.ExecSeg
public import ProofLib.GenPlacedFetches
public import ProofLib
public meta import ProofLib.ProgramReflection

/-!
# Placement-Generic `<SystemTime as Add<Duration>>::add`

Proves total correctness and overflow-panic behavior for
`<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add` (`timeAdd_ok` and
`timeAdd_subroutineOk`) against `timeAddSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open VerifiedLibraries.RustStd.TimeAddLemmas

/-! ## Extern Symbol and Panic Demangler -/

/-- Mangled `core::option::expect_failed` undefined symbol in `timeMultiLib.blocks[2].externs`. -/
abbrev rustTimeExpectFailedSym : String :=
  "_RNvNtCs2kXltWtc1W_4core6option13expect_failed"

/-- Demangle `timeMultiLib` panic extern symbols to the canonical names recognized by `Rust.withPanics`. -/
def timeDemangle (e : String) : String :=
  if e = rustTimeExpectFailedSym then "core::option::expect_failed" else e

/-- Extern hook lookup for `timeMultiLib`: applies `Rust.withPanics` after `timeDemangle`. -/
def timeExterns (hooks : String → Option (State → State) := fun _ => none) :
    String → Option (State → State) :=
  fun e => Rust.withPanics hooks (timeDemangle e)

theorem timeExterns_expectFailed (hooks : String → Option (State → State)) :
    timeExterns hooks rustTimeExpectFailedSym = some Rust.panicked := by
  have hc : [ "core::result::unwrap_failed",
    "core::option::unwrap_failed",
    "core::option::expect_failed",
    "core::slice::index::slice_start_index_len_fail",
    "core::slice::index::slice_end_index_len_fail",
    "core::slice::index::slice_index_order_fail",
    "core::slice::index::slice_index_fail",
    "alloc::raw_vec::handle_error",
    "alloc::raw_vec::capacity_overflow",
    "alloc::alloc::handle_alloc_error" ].contains "core::option::expect_failed" = true :=
    List.contains_iff_mem.mpr (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hp : Rust.isPanicSymbol "core::option::expect_failed" = true := by
    unfold Rust.isPanicSymbol
    rw [hc, Bool.or_true]
  have hdem : timeDemangle rustTimeExpectFailedSym = "core::option::expect_failed" := by
    unfold timeDemangle
    exact ite_eq_left_iff.mpr (fun h => False.elim (h rfl))
  unfold timeExterns
  rw [hdem]
  unfold Rust.withPanics
  rw [hp]
  rfl

/-! ## Placement Projections -/

def timeLib02 : PlacedLib := timeMultiLib.blockLib 2
def timePl02 [TimePlacement] : Placement := timeMultiLib.blockPlacement TimePlacement.mpl 2
theorem timePlaceable02 [TimePlacement] : timeLib02.Placeable timePl02 :=
  timeMultiLib.placeable_blockLib (by decide) TimePlacement.placeable
def timePC02 [TimePlacement] : Program := timeLib02.program timePl02

def timeProg02 : Program :=
  { code := timeLib02.text.code, symbols := timeLib02.text.symbols }
def timeTree02 : WordTree := word_tree_of% timeProg02
theorem time02_code_eq : timeLib02.text.code = timeTree02.toBytes := by rfl_kernel
theorem time02_tree_size : timeTree02.checkSize? = some 24 := by rfl_kernel
def timeSymChars02 : List (List Char × Nat) := sym_chars_of% timeProg02
theorem time02_symbols_eq : timeLib02.text.symbols = toStringSymbols timeSymChars02 := by rfl_kernel
theorem time02_symbols_fresh : allFreshCharSymbols timeSymChars02 = true := by rfl_kernel

section
set_option linter.literalFetch false
gen_placed_fetches timePC02 timeLib02 timeTree02 time02_code_eq time02_tree_size
  via_placement timePl02 timePlaceable02 [0x0 → 0x5c]
gen_placed_fnOffs timePC02 timeLib02 timeSymChars02 time02_symbols_eq time02_symbols_fresh
end

theorem timeBlockNoSvc0_02 : checkBlockNoSvc0 (timeMultiLib.blockLib 2).text = true := by decide

/-! ## Pure-Segment Lifting -/

private theorem strip_codeLoaded_local {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem strip_execOnlyIn_local (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) :=
  fun _ hpx => of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running_block {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem steps_rebase_lift_block {P R_j : Program}
    (hext_blk : ∀ off : Nat, off < R_j.code.length →
      P.externAt? (R_j.base + BitVec.ofNat 64 off) = none)
    (hext_R : ∀ pc, R_j.externAt? pc = none)
    (hall : R_j.allInstrs (fun i => !i.isSvc0) = true)
    {s1' sf' : State} (hsteps : Steps R_j s1' sf') (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep R_j) s1 → R_j.CodeLoaded s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (ProofLib.progKeep R_j) sf ∧
        Steps P s1 sf ∧ ProofLib.NonSyscallPreserved s1 sf := by
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, ProofLib.NonSyscallPreserved.refl s1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1
    have hrb' : sb'.status = .Running := steps_start_running_block hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ => rw [hext_R] at he; cases he
    | extern_fault _ he _ => rw [hext_R] at he; cases he
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hL1' : R_j.CodeLoaded (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_codeLoaded_local hL1
      have hexec' : R_j.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_execOnlyIn_local R_j s1.mem
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall hL1' hexec' _ inst hfe'
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).pc = s1.pc := by cases s1; rfl
        have hmem_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem =
            ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem := by cases s1; rfl
        rw [hpc_eq, hmem_eq] at hfe'
        unfold Program.fetchMem at hfe' ⊢
        rw [hext_R] at hfe'
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
          split at hfe'
          · contradiction
          · rename_i hce'
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
            have hkeep0 : ProofLib.progKeep R_j s1.pc = true := by
              have hce0 := hce'
              unfold Memory.canExec at hce0
              rw [Memory.allPerm_iff] at hce0
              have hx0 := hce0 0 (by omega)
              have hk := (ProofLib.strip_perm_x_imp hx0).2
              simpa using hk
            have hoff_lt : (s1.pc - R_j.base).toNat < R_j.code.length :=
              of_decide_eq_true hkeep0
            have hpc_off : R_j.base + BitVec.ofNat 64 (s1.pc - R_j.base).toNat = s1.pc := by
              simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
              bv_lin
            have hext_P_pc : P.externAt? s1.pc = none :=
              hpc_off ▸ hext_blk (s1.pc - R_j.base).toNat hoff_lt
            rw [hext_P_pc]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
              hal_pc, ne_eq, not_true_eq_false]
            have hce : s1.mem.canExec s1.pc 4 = true := by
              unfold Memory.canExec at hce' ⊢
              rw [Memory.allPerm_iff] at hce' ⊢
              intro k hk
              have hxk := hce' k hk
              rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
            have hr32 :
                (ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem).read32 s1.pc =
                  s1.mem.read32 s1.pc := by
              simp [Memory.read32, ProofLib.strip_read8]
            rw [hr32] at hfe'
            simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact hfe'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'
          contradiction
      have hev_R : R_j.evalInst inst (ProofLib.stripS (ProofLib.progKeep R_j) s1) =
          ProofLib.stripS (ProofLib.progKeep R_j) (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      obtain ⟨sf, hsf_eq, hsteps_P, hnsp_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_R (hstep_P.codeLoaded hL1)
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P,
        ProofLib.NonSyscallPreserved.trans
          (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1) hnsp_rest⟩

private theorem sepWPp_seg_block2_pure [TimePlacement] {P : Program}
    (hext_blk : ∀ off : Nat, off < 96 →
      P.externAt? (timeMpl.base 2 + BitVec.ofNat 64 off) = none)
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : timeMultiLib.CodeLoaded timeMpl s.mem)
    (hseg : ∀ s' : State, SameCpuState s' s →
      SepWP (timePC02.rebase timePl02.base (fun _ => none)) mid s' Pre (fun sm' Pm =>
        ∀ sm : State, SameCpuState sm sm' → timeMultiLib.CodeLoaded timeMpl sm.mem →
          ProofLib.NonSyscallPreserved s sm → SepWPp P ret sm Pm Q Qp oom)) :
    SepWPp P ret s Pre Q Qp oom := by
  let R_2 : Program := timePC02.rebase timePl02.base (fun _ => none)
  let keep := ProofLib.progKeep R_2
  have hR_eq : R_2 = (timeMultiLib.blockProgram timeMpl 2).rebase (timeMpl.base 2) (fun _ => none) := rfl
  have hL_R : R_2.CodeLoaded s.mem := (hcl 2 (by decide)).of_base_code rfl rfl
  have hext_R : ∀ pc, R_2.externAt? pc = none := by
    intro pc; rw [hR_eq]; exact MultiPlacedLib.externAt?_blockProgram_rebase_none _ _ _ _ _
  have hall : R_2.allInstrs (fun i => !i.isSvc0) = true := by
    rw [hR_eq]
    exact blockProgram_rebase_allInstrs_not_isSvc0 timeMultiLib timeMpl 2 timeBlockNoSvc0_02
  have hlen_R : R_2.code.length = 96 := by
    have hc : R_2.code = timeLib02.text.patched timePl02 := rfl
    rw [hc, Obj.CodeBlock.length_patched, length_text_of_tree time02_code_eq time02_tree_size]
  have hext_R_blk : ∀ off : Nat, off < R_2.code.length →
      P.externAt? (R_2.base + BitVec.ofNat 64 off) = none := by
    rw [hlen_R]
    exact hext_blk
  intro R hm hL_P
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hm
  have hcpu_in : SameCpuState (ProofLib.stripS keep s) s :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨sm', hsteps', hout'⟩ :=
    SepWP.to_reaches_pc (hseg (ProofLib.stripS keep s) hcpu_in) hm_strip
      (strip_codeLoaded_local hL_R)
  rcases hout' with ⟨_, hrun_m', Pm, hmm', hcont⟩ | ⟨_, hoom⟩
  · obtain ⟨sm, hsm_eq, hsteps_P, hnsp⟩ :=
      steps_rebase_lift_block hext_R_blk hext_R hall hsteps' hrun_m' s rfl hL_R
    have hcl_m : timeMultiLib.CodeLoaded timeMpl sm.mem :=
      fun k hk => hsteps_P.codeLoaded (hcl k hk)
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := fun a => congrFun hnsp.2.1 a
    have hmm'_mem : ProofLib.stripExecOutside keep sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keep sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hwp_cont := hcont sm (SameCpuState.of_stripS_left hsm_eq) hcl_m hnsp
    obtain ⟨sf, hsteps2, hout2⟩ := hwp_cont R hmm (hsteps_P.codeLoaded hL_P)
    exact ⟨sf, hsteps_P.trans hsteps2, hout2⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩
    exact False.elim hf

/-! ## Panic Tail and Main Contract -/

section
arm64_proof_prelude

private theorem timeAdd_panic_tail [TimePlacement] {s : State} {sp0 : BitVec 64}
    {post : State → SepProp → Prop}
    (hpc : s.pc = timePl02.base + 68#64) (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp0) (hsp_al : sp0 &&& 15#64 == 0#64)
    (hd : ∀ sm : State, sm.pc = timeMultiLib.resolve timeMpl rustTimeExpectFailedSym →
      sm.status = .Running →
      ∀ w0' w1' : BitVec 64, post sm (((sp0 - 16#64) ↦₆₄ w0') ∗ ((sp0 - 8#64) ↦₆₄ w1'))) :
    SepWP (timePC02.rebase timePl02.base (fun _ => none))
      (timeMultiLib.resolve timeMpl rustTimeExpectFailedSym) s (stackFrameAt sp0 16) post := by
  rw [timeAdd_stackFrameAt16_eq, ← hsp_eq]
  apply SepWP.exists_left; intro w0
  apply SepWP.exists_left; intro w1
  have hsp' : s.spAligned = true := by
    simp only [State.spAligned, hsp_eq]
    exact hsp_al
  wp_sym_steps
  have hpc_f :
      timePl02.base + 92#64 + (timePl02.ρ rustTimeExpectFailedSym - timePl02.base - 92#64) =
        timeMultiLib.resolve timeMpl rustTimeExpectFailedSym := by
    change timePl02.base + 92#64 +
      (timeMultiLib.resolve timeMpl rustTimeExpectFailedSym - timePl02.base - 92#64) =
      timeMultiLib.resolve timeMpl rustTimeExpectFailedSym
    bv_omega
  refine SepWP.done ?_ (by simpa [arm64_norm] using hrun) ?_
  · dsimp only [State.setMem, State.setPC]
    exact hpc_f
  · rw [hsp_eq]
    refine hd _ ?_ (by simpa [arm64_norm] using hrun) _ _
    dsimp only [State.setMem, State.setPC]
    exact hpc_f

/-- Program-generic contract for `<SystemTime as Add<Duration>>::add` (`timeAddSym`, block `2` of
    `timeMultiLib`): holds on any `P : Program` that has no hooks inside the 96-byte body of
    `TimeAdd` and hooks `rustTimeExpectFailedSym` with `Rust.panicked`. -/
theorem timeAdd_ok {P : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hext_blk : ∀ off : Nat, off < 96 →
      P.externAt? (mpl.base 2 + BitVec.ofNat 64 off) = none)
    (hpanic : P.externAt? (timeMultiLib.resolve mpl rustTimeExpectFailedSym) =
      some Rust.panicked) :
    subroutine_ok P (timeMultiLib.fnAddr mpl timeAddSym)
      (timeMultiLib.withCodeLoaded mpl timeAddSpec) := by
  letI : TimePlacement := ⟨mpl, hpl⟩
  rw [fnAddr_eq_base hpl 2 timeAddSym (by decide) (by decide)]
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨t, d⟩ R s0 hpc hrun hpre hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, timeAddSpec] at hpre ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hn1, hn2⟩, hpre⟩
  rw [← sepConj_assoc, sepConj_comm (stackFrameAt s0.sp 16), sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hmem0⟩
  refine ⟨stackFrameAt s0.sp 16, hmem0, ?_⟩
  let secs : Int := t.sec.toInt + (d.secs.toNat : Int)
  let nsec : Nat := t.nsec.toNat + d.nanos.toNat
  by_cases hA : (2 ^ 63 - 1 : Int) < secs
  ·
    have htca : timespecCheckedAdd t d = none := by
      unfold timespecCheckedAdd
      simp only [secs, hA, ↓reduceIte]
    apply sepWPp_seg_block2_pure hext_blk hcl
      (mid := timeMultiLib.resolve mpl rustTimeExpectFailedSym)
    intro s0' hcpu0
    have hpc0' : s0'.pc = timePl02.base := hcpu0.pc_eq.trans hpc
    have hrun0' : s0'.status = .Running := hcpu0.status_eq.trans hrun
    have hx0' : s0'.readReg64 .x0 = t.sec := (hcpu0.readReg64 .x0).trans hx0
    have hx2' : s0'.readReg64 .x2 = d.secs := (hcpu0.readReg64 .x2).trans hx2
    wp_sym_steps
    rw [timeAdd_tbnz_guard, decide_eq_true hA]
    simp only [beq_self_eq_true, ↓reduceIte]
    refine timeAdd_panic_tail rfl (by simpa [arm64_norm] using hrun0')
      (by simpa [arm64_norm] using hcpu0.sp_eq) hsp ?_
    intro sm' hpc_m' hrun_m' w0' w1' sm hcpu_m _hcl_m hnsp_m
    have hpc_m : sm.pc = timeMultiLib.resolve mpl rustTimeExpectFailedSym :=
      hcpu_m.pc_eq.trans hpc_m'
    have hrun_m : sm.status = .Running := hcpu_m.status_eq.trans hrun_m'
    refine SepWPp.panic hrun_m (hpc_m ▸ hpanic) ?_
    intro hm_pan
    dsimp only [Rust.panicked] at hm_pan ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htca, hnsp_m.1, hnsp_m.2.2.2.2.2.2⟩, ?_⟩
    exact Satisfies.mono (sepConj_mono_left (timeAdd_stackFrameAt16_fold s0.sp w0' w1')) hm_pan
  ·
    obtain ⟨hsec_add, _, hsec_lo, hsec_hi⟩ :=
      timeAdd_sec_add_no_overflow t.sec d.secs hA
    by_cases hB2 : 10 ^ 9 ≤ nsec
    ·
      have hnlt : ¬ (¬ (10 ^ 9 ≤ t.nsec.toNat + d.nanos.toNat)) := fun h => h hB2
      by_cases hB2a : (2 ^ 63 - 1 : Int) < secs + 1
      ·
        have htca : timespecCheckedAdd t d = none := by
          unfold timespecCheckedAdd
          simp only [secs, nsec, hA, hB2, hB2a, ↓reduceIte]
        apply sepWPp_seg_block2_pure hext_blk hcl
          (mid := timeMultiLib.resolve mpl rustTimeExpectFailedSym)
        intro s0' hcpu0
        have hpc0' : s0'.pc = timePl02.base := hcpu0.pc_eq.trans hpc
        have hrun0' : s0'.status = .Running := hcpu0.status_eq.trans hrun
        have hx0' : s0'.readReg64 .x0 = t.sec := (hcpu0.readReg64 .x0).trans hx0
        have hx1' : BitVec.setWidth 32 (s0'.readReg64 (.gpr 1#5)) = t.nsec :=
          (hcpu0.readReg32 .x1).trans hx1
        have hx2' : s0'.readReg64 .x2 = d.secs := (hcpu0.readReg64 .x2).trans hx2
        have hx3' : BitVec.setWidth 32 (s0'.readReg64 (.gpr 3#5)) = d.nanos :=
          (hcpu0.readReg32 .x3).trans hx3
        wp_sym_steps
        rw [timeAdd_tbnz_guard, decide_eq_false hA]
        simp only [beq_iff_eq, Bool.false_eq_true, ↓reduceIte]
        wp_sym_steps
        rw [timeAdd_nsec_ult_billion t.nsec d.nanos hn1 hn2, decide_eq_false hnlt]
        simp only [Bool.false_eq_true, ↓reduceIte]
        wp_sym_steps
        rw [timeAdd_carry_vs_guard secs hsec_lo hsec_hi, decide_eq_true hB2a]
        simp only [↓reduceIte]
        refine timeAdd_panic_tail rfl (by simpa [arm64_norm] using hrun0')
          (by simpa [arm64_norm] using hcpu0.sp_eq) hsp ?_
        intro sm' hpc_m' hrun_m' w0' w1' sm hcpu_m _hcl_m hnsp_m
        have hpc_m : sm.pc = timeMultiLib.resolve mpl rustTimeExpectFailedSym :=
          hcpu_m.pc_eq.trans hpc_m'
        have hrun_m : sm.status = .Running := hcpu_m.status_eq.trans hrun_m'
        refine SepWPp.panic hrun_m (hpc_m ▸ hpanic) ?_
        intro hm_pan
        dsimp only [Rust.panicked] at hm_pan ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨htca, hnsp_m.1, hnsp_m.2.2.2.2.2.2⟩, ?_⟩
        exact Satisfies.mono (sepConj_mono_left (timeAdd_stackFrameAt16_fold s0.sp w0' w1')) hm_pan
      ·
        have htca : timespecCheckedAdd t d =
            some { sec := BitVec.ofInt 64 (secs + 1), nsec := BitVec.ofNat 32 (nsec - 10 ^ 9) } := by
          unfold timespecCheckedAdd
          simp only [secs, nsec, hA, hB2, hB2a, ↓reduceIte]
        apply sepWPp_seg_block2_pure hext_blk hcl (mid := s0.readReg64 Reg.lr)
        intro s0' hcpu0
        have hpc0' : s0'.pc = timePl02.base := hcpu0.pc_eq.trans hpc
        have hrun0' : s0'.status = .Running := hcpu0.status_eq.trans hrun
        have hx0' : s0'.readReg64 .x0 = t.sec := (hcpu0.readReg64 .x0).trans hx0
        have hx1' : BitVec.setWidth 32 (s0'.readReg64 (.gpr 1#5)) = t.nsec :=
          (hcpu0.readReg32 .x1).trans hx1
        have hx2' : s0'.readReg64 .x2 = d.secs := (hcpu0.readReg64 .x2).trans hx2
        have hx3' : BitVec.setWidth 32 (s0'.readReg64 (.gpr 3#5)) = d.nanos :=
          (hcpu0.readReg32 .x3).trans hx3
        wp_sym_steps
        rw [timeAdd_tbnz_guard, decide_eq_false hA]
        simp only [beq_iff_eq, Bool.false_eq_true, ↓reduceIte]
        wp_sym_steps
        rw [timeAdd_nsec_ult_billion t.nsec d.nanos hn1 hn2, decide_eq_false hnlt]
        simp only [Bool.false_eq_true, ↓reduceIte]
        wp_sym_steps
        rw [timeAdd_carry_vs_guard secs hsec_lo hsec_hi, decide_eq_false hB2a]
        simp only [Bool.false_eq_true, ↓reduceIte]
        wp_sym_steps
        have hlr0 : s0'.readReg64 (.gpr 30#5) = s0.readReg64 Reg.lr := hcpu0.readReg64 .lr
        refine SepWP.done ?_ (by simpa [arm64_norm] using hrun0') ?_
        · dsimp only [State.setPC]
          exact hlr0
        · intro sm hcpu_m _hcl_m hnsp_m
          have hpc_m : sm.pc = s0.readReg64 Reg.lr := by
            rw [hcpu_m.pc_eq]
            dsimp only [State.setPC]
            exact hlr0
          have hrun_m : sm.status = .Running := by
            rw [hcpu_m.status_eq]; simpa [arm64_norm] using hrun0'
          have hsp_m : sm.sp = s0.sp := by
            rw [hcpu_m.sp_eq]; simpa [arm64_norm] using hcpu0.sp_eq
          have hcs_m : CalleeSavedPreserved s0 sm :=
            hcpu0.calleeSavedPreserved hcpu_m
              (by simp [CalleeSavedPreserved, calleeSavedVRegs, arm64_norm])
          refine SepWPp.done hpc_m hrun_m ⟨?_, hsp_m, hcs_m⟩
          intro hm_ret
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨⟨_, htca, ?_, ?_⟩, hnsp_m.1, hnsp_m.2.2.2.2.2.2⟩, hm_ret⟩
          · rw [hcpu_m.readReg64 .x0]
            simp only [State.readReg64_setPC, State.readReg64_setPState,
              State.readReg64_writeReg64, Reg.x0, ↓reduceIte]
            exact (timeAdd_carry_v_eq_overflow (BitVec.ofInt 64 secs) secs rfl hsec_lo hsec_hi).2
          · rw [hcpu_m.readReg64 .x1, Reg.x1, State.readReg64_setPC, State.readReg64_setPState,
              State.readReg64_writeReg64_gpr_same _ _ _ _ rfl rfl]
            exact congrArg (BitVec.setWidth 64) (timeAdd_nsec_sub_billion t.nsec d.nanos hn1 hn2 hB2)
    ·
      have htca : timespecCheckedAdd t d =
          some { sec := BitVec.ofInt 64 secs, nsec := BitVec.ofNat 32 nsec } := by
        unfold timespecCheckedAdd
        simp only [secs, nsec, hA, hB2, ↓reduceIte]
      apply sepWPp_seg_block2_pure hext_blk hcl (mid := s0.readReg64 Reg.lr)
      intro s0' hcpu0
      have hpc0' : s0'.pc = timePl02.base := hcpu0.pc_eq.trans hpc
      have hrun0' : s0'.status = .Running := hcpu0.status_eq.trans hrun
      have hx0' : s0'.readReg64 .x0 = t.sec := (hcpu0.readReg64 .x0).trans hx0
      have hx1' : BitVec.setWidth 32 (s0'.readReg64 (.gpr 1#5)) = t.nsec :=
        (hcpu0.readReg32 .x1).trans hx1
      have hx2' : s0'.readReg64 .x2 = d.secs := (hcpu0.readReg64 .x2).trans hx2
      have hx3' : BitVec.setWidth 32 (s0'.readReg64 (.gpr 3#5)) = d.nanos :=
        (hcpu0.readReg32 .x3).trans hx3
      wp_sym_steps
      rw [timeAdd_tbnz_guard, decide_eq_false hA]
      simp only [beq_iff_eq, Bool.false_eq_true, ↓reduceIte]
      wp_sym_steps
      rw [timeAdd_nsec_ult_billion t.nsec d.nanos hn1 hn2, decide_eq_true hB2]
      simp only [↓reduceIte]
      wp_sym_steps
      have hlr0 : s0'.readReg64 (.gpr 30#5) = s0.readReg64 Reg.lr := hcpu0.readReg64 .lr
      refine SepWP.done ?_ (by simpa [arm64_norm] using hrun0') ?_
      · dsimp only [State.setPC]
        exact hlr0
      · intro sm hcpu_m _hcl_m hnsp_m
        have hpc_m : sm.pc = s0.readReg64 Reg.lr := by
          rw [hcpu_m.pc_eq]
          dsimp only [State.setPC]
          exact hlr0
        have hrun_m : sm.status = .Running := by
          rw [hcpu_m.status_eq]; simpa [arm64_norm] using hrun0'
        have hsp_m : sm.sp = s0.sp := by
          rw [hcpu_m.sp_eq]; simpa [arm64_norm] using hcpu0.sp_eq
        have hcs_m : CalleeSavedPreserved s0 sm :=
          hcpu0.calleeSavedPreserved hcpu_m
            (by simp [CalleeSavedPreserved, calleeSavedVRegs, arm64_norm])
        refine SepWPp.done hpc_m hrun_m ⟨?_, hsp_m, hcs_m⟩
        intro hm_ret
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨⟨_, htca, ?_, ?_⟩, hnsp_m.1, hnsp_m.2.2.2.2.2.2⟩, hm_ret⟩
        · rw [hcpu_m.readReg64 .x0]
          simp only [State.readReg64_setPC, State.readReg64_setPState,
            State.readReg64_writeReg64, Reg.x0, ↓reduceIte]
          try rfl
        · rw [hcpu_m.readReg64 .x1, Reg.x1, State.readReg64_setPC, State.readReg64_setPState,
            State.readReg64_writeReg64_gpr_ne _ _ _ _ rfl rfl,
            State.readReg64_writeReg64_gpr_same _ _ _ _ rfl rfl]
          exact congrArg (BitVec.setWidth 64) (timeAdd_nsec_add_toNat t.nsec d.nanos hn1 hn2).2

end

/-! ## `MultiPlacedLib.subroutineOk` Corollaries -/

/-- `MultiPlacedLib.subroutineOk` for `timeAddSym` under any extern table mapping
    `rustTimeExpectFailedSym` to `Rust.panicked`. -/
theorem timeAdd_subroutineOk_of_panic {externs : String → Option (State → State)}
    (hpanic : externs rustTimeExpectFailedSym = some Rust.panicked) :
    timeMultiLib.subroutineOk timeAddSym (fun _ => timeAddSpec) externs := by
  refine ⟨by decide, 2, 0, by decide, fun mpl hpl => ?_⟩
  refine timeAdd_ok hpl (fun off hoff => ?_) ?_
  · have hP2 : (timeMultiLib.blockLib 2).text.Placeable (timeMultiLib.blockPlacement mpl 2) :=
      hpl.blocks_ok 2 (by decide)
    have hlen : 0 + 96 ≤ (timeMultiLib.blockLib 2).text.code.length := by
      change 0 + 96 ≤ timeLib02.text.code.length
      rw [length_text_of_tree time02_code_eq time02_tree_size]; omega
    have hhf := PlacedLib.hookFree_program_noOverrides
      (lib := timeMultiLib.blockLib 2) (pl := timeMultiLib.blockPlacement mpl 2)
      (X := externs) (svc := Syscall.standard) hP2 hlen
    have hoff_eq :
        (mpl.base 2 + BitVec.ofNat 64 off -
          (timeMultiLib.blockProgram mpl 2 externs).base).toNat = off := by
      change (mpl.base 2 + BitVec.ofNat 64 off - mpl.base 2).toNat = off
      rw [Program.add_ofNat_sub_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold Program.externAt?
    rw [hoff_eq]
    exact Program.hookAtOff?_eq_none_of_hookFree hhf (Nat.zero_le _) hoff
  · have hnd :
        ((timeMultiLib.blockLib 2).text.externs.map fun e' =>
          ((timeMultiLib.blockPlacement mpl 2).ρ e' -
            (timeMultiLib.blockPlacement mpl 2).base).toNat).Nodup := by
      have hext : (timeMultiLib.blockLib 2).text.externs = [rustTimeExpectFailedSym] := rfl
      rw [hext]; simp
    have hmem : rustTimeExpectFailedSym ∈ (timeMultiLib.blockLib 2).text.externs := by decide
    have hextAt := PlacedLib.externAt?_program
      (lib := timeMultiLib.blockLib 2) (pl := timeMultiLib.blockPlacement mpl 2)
      (X := externs) (O := fun _ => none) (svc := Syscall.standard) hnd hmem
    change ((timeMultiLib.blockLib 2).program (timeMultiLib.blockPlacement mpl 2) externs).externAt?
        ((timeMultiLib.blockPlacement mpl 2).ρ rustTimeExpectFailedSym) = some Rust.panicked
    rw [hextAt, hpanic]
    rfl

/-- Canonical `MultiPlacedLib.subroutineOk` for `timeAddSym` under `timeExterns hooks`. -/
theorem timeAdd_subroutineOk
    (hooks : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeAddSym (fun _ => timeAddSpec) (timeExterns hooks) :=
  timeAdd_subroutineOk_of_panic (timeExterns_expectFailed hooks)

end VerifiedLibraries.RustStd
