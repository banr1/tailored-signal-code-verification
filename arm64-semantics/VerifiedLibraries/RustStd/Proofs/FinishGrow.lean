/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.SmallProbeRead
public import ProofLib.GenPlacedFetches
public meta import ProofLib.ProgramReflection

/-!
# Placement-Generic `<alloc::raw_vec::RawVecInner>::finish_grow`

Proves `rustFinishGrow_ok` and `rustFinishGrow_okWhere` against `rustFinishGrowSpec A finishStack`
for block `22` (`<alloc::raw_vec::RawVecInner>::finish_grow`, `180` B) of `rustStdIoMultiLib`
over any allocator `(A : RustStdAlloc oom)`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.literalFetch false

namespace VerifiedLibraries.RustStd.Io

open Arm64 Arm64.Obj Arm64.Process ProofLib VerifiedLibraries.Musl
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup

/-! ## Extern Symbols and Contract -/

abbrev finishGrowIoSym : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [rust_std_io]"

abbrev rustAllocIoSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"

abbrev rustReallocIoSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc"

abbrev rustNoAllocShimIoSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"

/-- No-op contract for `__rustc::__rust_no_alloc_shim_is_unstable_v2()`. -/
def rustAllocShimSpec : Spec Unit where
  pre := fun _ s0 => Rust.hookFrame s0.sp
  post := fun _ s0 sf =>
    ⌜AllocCallPreserved s0 sf ∧ sf.brk = s0.brk⌝ ∗ Rust.hookFrame s0.sp
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Contract for `<alloc::raw_vec::RawVecInner>::finish_grow` specialized to `u8`
    (`elem_align = 1`, `elem_size = 1`), generic in `oom` and `(A : RustStdAlloc oom)`.
    Writes `[outPtr] = 0` with the reallocated `(newPtr, newCap)` on success (`newCap < 2 ^ 63`),
    `[outPtr] = 1` leaving `rustStdVecBuf` and `A.pool` unchanged on `CapacityOverflow` or
    null allocation (`NullAllowed newCap 1`), or exits via `onOom`. -/
def rustFinishGrowSpec {oom : State → State → Prop} (A : RustStdAlloc oom)
    (finishStack : Nat := Rust.hookStack) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 ×
      Nat × BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) where
  pre := fun (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, lb, lk) s0 =>
    ⌜s0.readReg64 .x0 = outPtr ∧
      s0.readReg64 .x1 = BitVec.ofNat 64 oldCap ∧
      s0.readReg64 .x2 = oldPtr ∧
      s0.readReg64 .x3 = BitVec.ofNat 64 newCap ∧
      s0.readReg64 .x4 = 1#64 ∧
      s0.readReg64 .x5 = 1#64 ∧
      0 < newCap ∧ newCap < 2 ^ 64 ∧
      bs.length ≤ newCap ∧
      (newCap < 2 ^ 63 → A.CanAlloc lb lk newCap 1)⌝ ∗
    (stackAt s0.sp (48 + finishStack) ∗
      vecHeader outPtr v0 v1 v2 ∗
      rustStdVecBuf A oldCap oldPtr bs ∗
      A.pool lb lk s0 ∗
      StdErrnoCell s0.tpidrEl0)
  post := fun (outPtr, _, _, _, oldCap, oldPtr, bs, newCap, lb, lk) s0 sf =>
    ∃∗ isErr : Bool,
      if isErr then
        ∃∗ errW1 : BitVec 64, ∃∗ errW2 : BitVec 64,
          ⌜AllocCallPreserved s0 sf ∧ NullAllowed newCap 1⌝ ∗
          (stackAt s0.sp (48 + finishStack) ∗
            vecHeader outPtr 1#64 errW1 errW2 ∗
            rustStdVecBuf A oldCap oldPtr bs ∗
            A.pool lb lk sf ∗
            StdErrnoCell s0.tpidrEl0)
      else
        ∃∗ newPtr : BitVec 64,
          ⌜AllocCallPreserved s0 sf ∧ newCap < 2 ^ 63⌝ ∗
          (stackAt s0.sp (48 + finishStack) ∗
            vecHeader outPtr 0#64 newPtr (BitVec.ofNat 64 newCap) ∗
            rustStdVecBuf A newCap newPtr bs ∗
            A.pool (rustVecGrowLb A lb oldCap newCap) (rustVecGrowLk lk oldCap) sf ∗
            StdErrnoCell s0.tpidrEl0)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun (_, _, _, _, _, _, _, newCap, _, _) s0 sf =>
    ⌜newCap < 2 ^ 63 ∧
      ∃ sm, IoFrame s0 sm ∧ sm.fs = s0.fs ∧ PoolPreserved s0 sm ∧ oom sm sf⌝

/-! ## Fetch Generation and Stepping Helpers -/

class RawVecGrowPlacement where
  mpl : MultiPlacement
  placeable : rustStdIoMultiLib.Placeable mpl

private def rvgLib22 : PlacedLib := rustStdIoMultiLib.blockLib 22
private def rvgPl22 [RawVecGrowPlacement] : Placement :=
  rustStdIoMultiLib.blockPlacement RawVecGrowPlacement.mpl 22
private theorem rvgPlaceable22 [RawVecGrowPlacement] : rvgLib22.Placeable rvgPl22 :=
  rustStdIoMultiLib.placeable_blockLib (by decide) RawVecGrowPlacement.placeable
private def rvgPC22 [RawVecGrowPlacement] : Program := rvgLib22.program rvgPl22

private def rvgProg22 : Program :=
  { code := rvgLib22.text.code, symbols := rvgLib22.text.symbols }
private def rvgTree22 : WordTree := word_tree_of% rvgProg22
private theorem rvg22_code_eq : rvgLib22.text.code = rvgTree22.toBytes := by rfl_kernel
private theorem rvg22_tree_size : rvgTree22.checkSize? = some 45 := by rfl_kernel

gen_placed_fetches rvgPC22 rvgLib22 rvgTree22 rvg22_code_eq rvg22_tree_size
  via_placement rvgPl22 rvgPlaceable22 [0x0 → 0xb0]

theorem rustIoBlockNoSvc0_22 : checkBlockNoSvc0 (rustStdIoMultiLib.blockLib 22).text = true := by
  decide

theorem resolve_eq_base {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (hpl : lib.Placeable mpl) (j : Nat) (sym : String)
    (hj : j < lib.blocks.length) (hl : lookup sym lib.blocks[j].symbols = some 0) :
    lib.resolve mpl sym = mpl.base j := by
  have hblk := lookupBlockSym_of_lookup hj hpl.symbols_nodup hl
  simp [MultiPlacedLib.resolve, hblk]

structure SameCpuOracleState (a b : State) : Prop extends SameCpuState a b where
  oracle_eq : a.oracle = b.oracle

private theorem strip_codeLoaded_rvg {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
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

private theorem strip_execOnlyIn_rvg (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := fun _ hpx =>
  of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running_rvg {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => exact h1.running_of_step

private theorem steps_rebase_lift_strip_rvg {P R_j : Program}
    (hext_P : ∀ pc, P.externAt? pc = none) (hext_R : ∀ pc, R_j.externAt? pc = none)
    (hall : R_j.allInstrs (fun i => !i.isSvc0) = true)
    {s1' sf' : State} (hsteps : Steps R_j s1' sf') (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep R_j) s1 → R_j.CodeLoaded s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (ProofLib.progKeep R_j) sf ∧
        Steps P s1 sf ∧ ProofLib.NonSyscallPreserved s1 sf := by
  induction hsteps with
  | refl => intro s1 hs1 _; exact ⟨s1, hs1, .refl s1, ProofLib.NonSyscallPreserved.refl s1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1
    have hrb' : sb'.status = .Running := steps_start_running_rvg hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases hrb'
    | extern _ he _ _ => rw [hext_R] at he; cases he
    | extern_fault _ he _ => rw [hext_R] at he; cases he
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by
        simpa [ProofLib.stripS, State.status_setMem] using hr1'
      have hL1' : R_j.CodeLoaded (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        by rw [ProofLib.stripS, State.mem_setMem]; exact strip_codeLoaded_rvg hL1
      have hexec' : R_j.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        by rw [ProofLib.stripS, State.mem_setMem]; exact strip_execOnlyIn_rvg R_j s1.mem
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall hL1' hexec' _ inst hfe'
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).pc = s1.pc := by
          simp [ProofLib.stripS]
        have hmem_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem =
            ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem := by
          simp [ProofLib.stripS]
        rw [hpc_eq, hmem_eq] at hfe'
        unfold Program.fetchMem at hfe' ⊢
        rw [hext_R] at hfe'; rw [hext_P]
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe' ⊢
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe' ⊢
          split at hfe'
          · contradiction
          · rename_i hce'
            have hce : s1.mem.canExec s1.pc 4 = true := by
              simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
              unfold Memory.canExec at hce' ⊢; rw [Memory.allPerm_iff] at hce' ⊢; intro k hk
              have hxk := hce' k hk
              rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
            have hr32 : (ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem).read32 s1.pc =
                s1.mem.read32 s1.pc := by simp [Memory.read32, ProofLib.strip_read8]
            rw [hr32] at hfe'
            simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hfe'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'; contradiction
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

/-- Pure-segment stepping across block `j` under `CodeLoadedWhere keep`, recording
    `SameCpuOracleState` and `sm.symtab = s.symtab` for `AllocCallPreserved` and `PoolPreserved`. -/
theorem sepWP_seg_rebase_pure_alloc {lib : MultiPlacedLib} {keep : Nat → Bool} {mpl : MultiPlacement}
    {P : Program} (hext : ∀ pc, P.externAt? pc = none)
    (j : Nat) (hj : j < lib.blocks.length ∧ keep j = true)
    (hchk : checkBlockNoSvc0 (lib.blockLib j).text = true := by decide)
    {mid target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : lib.CodeLoadedWhere keep mpl s.mem)
    (hseg : ∀ s' : State, SameCpuOracleState s' s →
      SepWP ((lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)) mid s' Pre (fun sm' Pm =>
        ∀ sm : State, SameCpuOracleState sm sm' → lib.CodeLoadedWhere keep mpl sm.mem →
          ProofLib.NonSyscallPreserved s sm → sm.symtab = s.symtab →
          SepWP P target_pc sm Pm post oom)) :
    SepWP P target_pc s Pre post oom := by
  let R_j := (lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)
  let keepExec := ProofLib.progKeep R_j
  have hL_R : R_j.CodeLoaded s.mem := (hcl j hj.1 hj.2).of_base_code rfl rfl
  have hext_R : ∀ pc, R_j.externAt? pc = none := by intro pc; simp [R_j]
  have hall : R_j.allInstrs (fun i => !i.isSvc0) = true :=
    blockProgram_rebase_allInstrs_not_isSvc0 lib mpl j hchk
  refine SepWP.of_reaches_pc fun R hm => ?_
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keepExec hm
  have hcpu_in : SameCpuOracleState (ProofLib.stripS keepExec s) s :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp [ProofLib.stripS]⟩
  obtain ⟨sm', hsteps', hout'⟩ :=
    SepWP.to_reaches_pc (hseg (ProofLib.stripS keepExec s) hcpu_in) hm_strip
      (by rw [ProofLib.stripS, State.mem_setMem]; exact strip_codeLoaded_rvg hL_R)
  rcases hout' with ⟨hpc_m', hrun_m', Pm, hmm', hcont⟩ | ⟨_, hoom⟩
  · obtain ⟨sm, hsm_eq, hsteps_P, hnsp⟩ :=
      steps_rebase_lift_strip_rvg hext hext_R hall hsteps' hrun_m' s rfl hL_R
    have hcl_m : lib.CodeLoadedWhere keep mpl sm.mem := hsteps_P.codeLoadedWhere hcl
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := fun a => congrFun hnsp.2.1 a
    have hmm'_mem : ProofLib.stripExecOutside keepExec sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keepExec sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hcpu_out : SameCpuOracleState sm sm' :=
      ⟨SameCpuState.of_stripS_left hsm_eq, by rw [hsm_eq]; simp [ProofLib.stripS]⟩
    have hwp_cont := hcont sm hcpu_out hcl_m hnsp hsteps_P.symtab_eq
    exact fun hL_P => by
      obtain ⟨sf, hsteps2, hout2⟩ := SepWP.to_reaches_pc hwp_cont hmm (hsteps_P.codeLoaded hL_P)
      exact ⟨sf, hsteps_P.trans hsteps2, hout2⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩; exact False.elim hf

theorem allocCallPreserved_of_seg {s s' sm' sm : State}
    (h_in : SameCpuOracleState s' s) (h_out : SameCpuOracleState sm sm')
    (hnsp : ProofLib.NonSyscallPreserved s sm) (hsym : sm.symtab = s.symtab)
    (htp : sm'.tpidrEl0 = s'.tpidrEl0) (hsig : sm'.sigActions = s'.sigActions)
    (horc : sm'.oracle = s'.oracle) :
    AllocCallPreserved s sm ∧ PoolPreserved s sm :=
  ⟨⟨hnsp.2.2.2.2.2.2, hnsp.1,
    h_out.toSameCpuState.sigActions_eq.trans (hsig.trans h_in.toSameCpuState.sigActions_eq),
    h_out.toSameCpuState.tpidrEl0_eq.trans (htp.trans h_in.toSameCpuState.tpidrEl0_eq),
    hnsp.2.2.2.1,
    h_out.oracle_eq.trans (horc.trans h_in.oracle_eq),
    hsym⟩,
   ⟨hnsp.2.2.2.1, hnsp.2.2.1,
    h_out.toSameCpuState.tpidrEl0_eq.trans (htp.trans h_in.toSameCpuState.tpidrEl0_eq)⟩⟩

theorem allocCallPreserved_trans {s0 s1 s2 : State}
    (h01 : AllocCallPreserved s0 s1) (h12 : AllocCallPreserved s1 s2) :
    AllocCallPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

theorem poolPreserved_trans {s0 s1 s2 : State}
    (h01 : PoolPreserved s0 s1) (h12 : PoolPreserved s1 s2) :
    PoolPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.trans h01.2.2⟩

def RvgHiCS (s0 s : State) : Prop :=
  s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0

theorem RvgHiCS.refl (s0 : State) : RvgHiCS s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem RvgHiCS.of_cs {s0 sm sf : State}
    (h : RvgHiCS s0 sm) (hcs : CalleeSavedPreserved sm sf) : RvgHiCS s0 sf :=
  ⟨hcs.readReg64_x22.trans h.1, hcs.readReg64_x23.trans h.2.1,
   hcs.readReg64_x24.trans h.2.2.1, hcs.readReg64_x25.trans h.2.2.2.1,
   hcs.readReg64_x26.trans h.2.2.2.2.1, hcs.readReg64_x27.trans h.2.2.2.2.2.1,
   hcs.readReg64_x28.trans h.2.2.2.2.2.2.1, hcs.vregs.trans h.2.2.2.2.2.2.2⟩

theorem RvgHiCS.of_seg {s0 s s' sm' sm : State}
    (h : RvgHiCS s0 s) (h_in : SameCpuOracleState s' s) (h_out : SameCpuOracleState sm sm')
    (hx22 : sm'.readReg64 .x22 = s'.readReg64 .x22)
    (hx23 : sm'.readReg64 .x23 = s'.readReg64 .x23)
    (hx24 : sm'.readReg64 .x24 = s'.readReg64 .x24)
    (hx25 : sm'.readReg64 .x25 = s'.readReg64 .x25)
    (hx26 : sm'.readReg64 .x26 = s'.readReg64 .x26)
    (hx27 : sm'.readReg64 .x27 = s'.readReg64 .x27)
    (hx28 : sm'.readReg64 .x28 = s'.readReg64 .x28)
    (hv : calleeSavedVRegs sm' = calleeSavedVRegs s') : RvgHiCS s0 sm :=
  ⟨(h_out.toSameCpuState.readReg64 .x22).trans (hx22.trans ((h_in.toSameCpuState.readReg64 .x22).trans h.1)),
   (h_out.toSameCpuState.readReg64 .x23).trans (hx23.trans ((h_in.toSameCpuState.readReg64 .x23).trans h.2.1)),
   (h_out.toSameCpuState.readReg64 .x24).trans (hx24.trans ((h_in.toSameCpuState.readReg64 .x24).trans h.2.2.1)),
   (h_out.toSameCpuState.readReg64 .x25).trans (hx25.trans ((h_in.toSameCpuState.readReg64 .x25).trans h.2.2.2.1)),
   (h_out.toSameCpuState.readReg64 .x26).trans (hx26.trans ((h_in.toSameCpuState.readReg64 .x26).trans h.2.2.2.2.1)),
   (h_out.toSameCpuState.readReg64 .x27).trans (hx27.trans ((h_in.toSameCpuState.readReg64 .x27).trans h.2.2.2.2.2.1)),
   (h_out.toSameCpuState.readReg64 .x28).trans (hx28.trans ((h_in.toSameCpuState.readReg64 .x28).trans h.2.2.2.2.2.2.1)),
   h_out.toSameCpuState.calleeSavedVRegs.trans (hv.trans (h_in.toSameCpuState.calleeSavedVRegs.trans h.2.2.2.2.2.2.2))⟩

theorem RvgHiCS.to_cs {s0 sf : State} (h : RvgHiCS s0 sf)
    (hx19 : sf.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : sf.readReg64 .x20 = s0.readReg64 .x20)
    (hx21 : sf.readReg64 .x21 = s0.readReg64 .x21)
    (hfp : sf.readReg64 .fp = s0.readReg64 .fp) : CalleeSavedPreserved s0 sf := by
  rw [CalleeSavedPreserved.iff_regs]
  exact ⟨hx19, hx20, hx21, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, hfp, h.2.2.2.2.2.2.2⟩

/-! ## Correctness of `finish_grow` -/

section
arm64_proof_prelude

@[local simp] private theorem umulh_one_left_64 (v : BitVec 64) :
    BitVec.setWidth 64 ((BitVec.setWidth 128 1#64 * BitVec.setWidth 128 v) >>> 64) = 0#64 := by
  have h1 : BitVec.setWidth 128 1#64 = 1#128 := rfl
  rw [h1]; apply BitVec.eq_of_toNat_eq; have hv := v.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.one_mul,
    Nat.mod_eq_of_lt (by omega : v.toNat < 340282366920938463463374607431768211456),
    Nat.shiftRight_eq_div_pow]
  omega

@[local simp] private theorem umulh_one128_left_64 (v : BitVec 64) :
    BitVec.setWidth 64 ((1#128 * BitVec.setWidth 128 v) >>> 64) = 0#64 :=
  umulh_one_left_64 v

private theorem satisfies_rustStdVecBuf_bounds_rvg {oom : State → State → Prop} {A : RustStdAlloc oom}
    {m : Memory} {cap : Nat} {ptr : BitVec 64} {bs : List (BitVec 8)} {R : SepProp}
    (h : m ⊨ rustStdVecBuf A cap ptr bs ∗ R) :
    bs.length ≤ cap ∧ cap < 2 ^ 63 ∧ ptr ≠ 0#64 := by
  unfold rustStdVecBuf at h; rw [sepConj_assoc, satisfies_pure_sepConj] at h; exact h.1

private def rvgSavedSlots22 (s0 : State) (st3 : BitVec 64) : SepProp :=
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗ ((s0.sp - 24#64) ↦₆₄ st3) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

private theorem rvgRealloc_pc [RawVecGrowPlacement] :
    rvgPl22.base + 88#64 + (rvgPl22.ρ rustReallocIoSym - rvgPl22.base - 88#64) =
      rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl rustReallocIoSym := by
  change rvgPl22.base + 88#64 +
    (rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl rustReallocIoSym - rvgPl22.base - 88#64) = _
  bv_lin

private theorem rvgShim_pc [RawVecGrowPlacement] :
    rvgPl22.base + 104#64 + (rvgPl22.ρ rustNoAllocShimIoSym - rvgPl22.base - 104#64) =
      rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl rustNoAllocShimIoSym := by
  change rvgPl22.base + 104#64 +
    (rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl rustNoAllocShimIoSym - rvgPl22.base - 104#64) = _
  bv_lin

private theorem rvgAlloc_pc [RawVecGrowPlacement] :
    rvgPl22.base + 116#64 + (rvgPl22.ρ rustAllocIoSym - rvgPl22.base - 116#64) =
      rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl rustAllocIoSym := by
  change rvgPl22.base + 116#64 +
    (rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl rustAllocIoSym - rvgPl22.base - 116#64) = _
  bv_lin

private def errnoCell (tp : BitVec 64) : SepProp := StdErrnoCell tp
private theorem errnoCell_eq (tp : BitVec 64) : StdErrnoCell tp = errnoCell tp := rfl

private theorem rustFinishGrow_epilogue_err [RawVecGrowPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext : ∀ pc, P.externAt? pc = none)
    {s0 s_ep : State} {outPtr v0 v1 v2 oldPtr st3 : BitVec 64}
    {oldCap newCap lb lk finishStack : Nat} {bs : List (BitVec 8)}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hstk_top : 48 + finishStack ≤ 2 ^ 64)
    (hcl : rustStdIoMultiLib.CodeLoadedWhere (· == 22) RawVecGrowPlacement.mpl s_ep.mem)
    (hpc : s_ep.pc = rvgPl22.base + 124#64) (hrun : s_ep.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : s_ep.sp = s0.sp - 48#64)
    (hx19 : s_ep.readReg64 (.gpr 19#5) = outPtr)
    (hx20 : s_ep.readReg64 (.gpr 20#5) = BitVec.ofNat 64 newCap)
    (hx21 : s_ep.readReg64 (.gpr 21#5) = 1#64)
    (hhi : RvgHiCS s0 s_ep) (hpres0 : AllocCallPreserved s0 s_ep) (hnull : NullAllowed newCap 1)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      post sf ((rustFinishGrowSpec A finishStack).post
        (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, lb, lk) s0 sf)) :
    SepWP P (s0.readReg64 .lr) s_ep
      (stackAt (s0.sp - 48#64) finishStack ∗ rvgSavedSlots22 s0 st3 ∗
        vecHeader outPtr v0 v1 v2 ∗ rustStdVecBuf A oldCap oldPtr bs ∗ A.pool lb lk s_ep ∗
        errnoCell s0.tpidrEl0)
      post oomProp := by
  apply sepWP_seg_rebase_pure_alloc (lib := rustStdIoMultiLib) (mpl := RawVecGrowPlacement.mpl)
    hext 22 (by decide) rustIoBlockNoSvc0_22 hcl (mid := s0.readReg64 .lr)
  intro se' hcpu_e; change SepWP (rvgPC22.rebase rvgPl22.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = rvgPl22.base + 124#64 := hcpu_e.toSameCpuState.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.toSameCpuState.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 48#64 := hcpu_e.toSameCpuState.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_e_in]; exact s0.spAligned_sub 48#64 hsp0
  have hx19_e' : se'.readReg64 (.gpr 19#5) = outPtr := (hcpu_e.toSameCpuState.readReg64 (.gpr 19#5)).trans hx19
  have hx20_e' : se'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 newCap :=
    (hcpu_e.toSameCpuState.readReg64 (.gpr 20#5)).trans hx20
  have hx21_e' : se'.readReg64 (.gpr 21#5) = 1#64 := (hcpu_e.toSameCpuState.readReg64 (.gpr 21#5)).trans hx21
  wp_conv_pre => simp only [rvgSavedSlots22, vecHeader, ← hsp_e_in,
    show s0.sp - 40#64 = se'.sp + 8#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 32#64 = se'.sp + 16#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 24#64 = se'.sp + 24#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 16#64 = se'.sp + 32#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 8#64 = se'.sp + 40#64 by rw [hsp_e_in]; bv_lin]
  wp_sym_steps
  refine SepWP.done (by rfl) (by simpa [arm64_norm] using hrun_e') fun sf hcpu_f _hcl_f hnsp_f hsym_f => ?_
  obtain ⟨hpres_ef, hpool_ef⟩ := allocCallPreserved_of_seg hcpu_e hcpu_f hnsp_f hsym_f
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpres_f : AllocCallPreserved s0 sf := allocCallPreserved_trans hpres0 hpres_ef
  have hpool_eq : A.pool lb lk s_ep = A.pool lb lk sf := (A.pool_transport lb lk s_ep sf hpool_ef).symm
  have hpc_f : sf.pc = s0.readReg64 .lr := by rw [hcpu_f.toSameCpuState.pc_eq]; rfl
  have hrun_f : sf.status = .Running :=
    hcpu_f.toSameCpuState.status_eq.trans (by simpa [arm64_norm] using hrun_e')
  have hsp_f : sf.sp = s0.sp := by rw [hcpu_f.toSameCpuState.sp_eq]; simp [arm64_norm]
  have hcs_f : CalleeSavedPreserved s0 sf :=
    (hhi.of_seg hcpu_e hcpu_f (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm])).to_cs
      (by rw [hcpu_f.toSameCpuState.readReg64 .x19]; simp [arm64_norm])
      (by rw [hcpu_f.toSameCpuState.readReg64 .x20]; simp [arm64_norm])
      (by rw [hcpu_f.toSameCpuState.readReg64 .x21]; simp [arm64_norm])
      (by rw [hcpu_f.toSameCpuState.readReg64 .fp]; simp [arm64_norm])
  refine SepWP.weaken_pre ?_ (SepWP.done hpc_f hrun_f (hcont sf hpc_f hrun_f hsp_f hcs_f))
  dsimp only [rustFinishGrowSpec]; refine Entails.sepExists_right true ?_; simp only [↓reduceIte]
  refine Entails.sepExists_right 1#64 (Entails.sepExists_right (BitVec.ofNat 64 newCap) ?_)
  rw [pure_sepConj_of_true (φ := AllocCallPreserved s0 sf ∧ NullAllowed newCap 1) ⟨hpres_f, hnull⟩,
      errnoCell_eq, hpool_eq, hsp_e_in, show 48 + finishStack = finishStack + 8 * 6 by omega,
      stackAt_split_cells s0.sp finishStack 6 (by omega)]
  dsimp only [cells, vecHeader]
  simp only [Nat.reduceMul, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, bv_lin_norm]
  refine Entails.sepExists_right (s0.readReg64 (.gpr 29#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 21#5)) <|
    Entails.sepExists_right st3 <|
    Entails.sepExists_right (s0.readReg64 (.gpr 20#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) (by sep_entail)

private theorem rustFinishGrow_epilogue_ok [RawVecGrowPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext : ∀ pc, P.externAt? pc = none)
    {s0 s_ep : State} {outPtr v0 v1 v2 oldPtr newPtr st3 : BitVec 64}
    {oldCap newCap lb lk finishStack : Nat} {bs : List (BitVec 8)}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hstk_top : 48 + finishStack ≤ 2 ^ 64)
    (hcl : rustStdIoMultiLib.CodeLoadedWhere (· == 22) RawVecGrowPlacement.mpl s_ep.mem)
    (hpc : s_ep.pc = rvgPl22.base + 140#64) (hrun : s_ep.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : s_ep.sp = s0.sp - 48#64)
    (hx0 : s_ep.readReg64 .x0 = newPtr)
    (hx19 : s_ep.readReg64 (.gpr 19#5) = outPtr)
    (hx20 : s_ep.readReg64 (.gpr 20#5) = BitVec.ofNat 64 newCap)
    (hhi : RvgHiCS s0 s_ep) (hpres0 : AllocCallPreserved s0 s_ep) (hcap_lt : newCap < 2 ^ 63)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      post sf ((rustFinishGrowSpec A finishStack).post
        (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, lb, lk) s0 sf)) :
    SepWP P (s0.readReg64 .lr) s_ep
      (stackAt (s0.sp - 48#64) finishStack ∗ rvgSavedSlots22 s0 st3 ∗
        vecHeader outPtr v0 v1 v2 ∗ rustStdVecBuf A newCap newPtr bs ∗
        A.pool (rustVecGrowLb A lb oldCap newCap) (rustVecGrowLk lk oldCap) s_ep ∗
        errnoCell s0.tpidrEl0)
      post oomProp := by
  apply sepWP_seg_rebase_pure_alloc (lib := rustStdIoMultiLib) (mpl := RawVecGrowPlacement.mpl)
    hext 22 (by decide) rustIoBlockNoSvc0_22 hcl (mid := s0.readReg64 .lr)
  intro se' hcpu_e; change SepWP (rvgPC22.rebase rvgPl22.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = rvgPl22.base + 140#64 := hcpu_e.toSameCpuState.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.toSameCpuState.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 48#64 := hcpu_e.toSameCpuState.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_e_in]; exact s0.spAligned_sub 48#64 hsp0
  have hx0_e' : se'.readReg64 (.gpr 0#5) = newPtr := (hcpu_e.toSameCpuState.readReg64 .x0).trans hx0
  have hx19_e' : se'.readReg64 (.gpr 19#5) = outPtr := (hcpu_e.toSameCpuState.readReg64 (.gpr 19#5)).trans hx19
  have hx20_e' : se'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 newCap :=
    (hcpu_e.toSameCpuState.readReg64 (.gpr 20#5)).trans hx20
  wp_conv_pre => simp only [rvgSavedSlots22, vecHeader, ← hsp_e_in,
    show s0.sp - 40#64 = se'.sp + 8#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 32#64 = se'.sp + 16#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 24#64 = se'.sp + 24#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 16#64 = se'.sp + 32#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 8#64 = se'.sp + 40#64 by rw [hsp_e_in]; bv_lin]
  wp_sym_steps
  refine SepWP.done (by rfl) (by simpa [arm64_norm] using hrun_e') fun sf hcpu_f _hcl_f hnsp_f hsym_f => ?_
  obtain ⟨hpres_ef, hpool_ef⟩ := allocCallPreserved_of_seg hcpu_e hcpu_f hnsp_f hsym_f
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpres_f : AllocCallPreserved s0 sf := allocCallPreserved_trans hpres0 hpres_ef
  have hpool_eq :
      A.pool (rustVecGrowLb A lb oldCap newCap) (rustVecGrowLk lk oldCap) s_ep =
        A.pool (rustVecGrowLb A lb oldCap newCap) (rustVecGrowLk lk oldCap) sf :=
    (A.pool_transport _ _ s_ep sf hpool_ef).symm
  have hpc_f : sf.pc = s0.readReg64 .lr := by rw [hcpu_f.toSameCpuState.pc_eq]; rfl
  have hrun_f : sf.status = .Running :=
    hcpu_f.toSameCpuState.status_eq.trans (by simpa [arm64_norm] using hrun_e')
  have hsp_f : sf.sp = s0.sp := by rw [hcpu_f.toSameCpuState.sp_eq]; simp [arm64_norm]
  have hcs_f : CalleeSavedPreserved s0 sf :=
    (hhi.of_seg hcpu_e hcpu_f (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm])).to_cs
      (by rw [hcpu_f.toSameCpuState.readReg64 .x19]; simp [arm64_norm])
      (by rw [hcpu_f.toSameCpuState.readReg64 .x20]; simp [arm64_norm])
      (by rw [hcpu_f.toSameCpuState.readReg64 .x21]; simp [arm64_norm])
      (by rw [hcpu_f.toSameCpuState.readReg64 .fp]; simp [arm64_norm])
  refine SepWP.weaken_pre ?_ (SepWP.done hpc_f hrun_f (hcont sf hpc_f hrun_f hsp_f hcs_f))
  dsimp only [rustFinishGrowSpec]
  refine Entails.sepExists_right false ?_; simp only [Bool.false_eq_true, ↓reduceIte]
  refine Entails.sepExists_right newPtr ?_
  rw [pure_sepConj_of_true (φ := AllocCallPreserved s0 sf ∧ newCap < 2 ^ 63) ⟨hpres_f, hcap_lt⟩,
      errnoCell_eq, hpool_eq, hsp_e_in, show 48 + finishStack = finishStack + 8 * 6 by omega,
      stackAt_split_cells s0.sp finishStack 6 (by omega)]
  dsimp only [cells, vecHeader]
  simp only [Nat.reduceMul, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, bv_lin_norm]
  refine Entails.sepExists_right (s0.readReg64 (.gpr 29#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 21#5)) <|
    Entails.sepExists_right st3 <|
    Entails.sepExists_right (s0.readReg64 (.gpr 20#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) (by sep_entail)

private theorem rustFinishGrow_zero_cap [RawVecGrowPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext : ∀ pc, P.externAt? pc = none)
    {s0 : State} {outPtr v0 v1 v2 oldPtr st0 st1 st2 st3 st4 st5 : BitVec 64}
    {newCap lb lk finishStack : Nat} {bs : List (BitVec 8)}
    {post : State → SepProp → Prop}
    (hstk : Rust.hookStack ≤ finishStack ∧ 48 + finishStack ≤ 2 ^ 64)
    (hshim : subroutine_ok P
      (rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl rustNoAllocShimIoSym) rustAllocShimSpec)
    (halloc : subroutine_ok P
      (rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl rustAllocIoSym) (rustStdAllocSpec A))
    (hcl : rustStdIoMultiLib.CodeLoadedWhere (· == 22) RawVecGrowPlacement.mpl s0.mem)
    (hpc : s0.pc = rvgPl22.base) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = outPtr) (hx1 : s0.readReg64 .x1 = 0#64)
    (hx3 : s0.readReg64 .x3 = BitVec.ofNat 64 newCap)
    (hx4 : s0.readReg64 .x4 = 1#64) (hx5 : s0.readReg64 .x5 = 1#64)
    (hold_nz : oldPtr ≠ 0#64) (hnew_pos : 0 < newCap) (hcap_lt : newCap < 2 ^ 63)
    (hbs_le0 : bs.length ≤ 0) (hcan : A.CanAlloc lb lk newCap 1)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      post sf ((rustFinishGrowSpec A finishStack).post
        (outPtr, v0, v1, v2, 0, oldPtr, bs, newCap, lb, lk) s0 sf)) :
    SepWP P (s0.readReg64 .lr) s0
      (stackAt (s0.sp - 48#64) finishStack ∗
        ((s0.sp - 48#64) ↦₆₄ st0) ∗ ((s0.sp - 40#64) ↦₆₄ st1) ∗
        ((s0.sp - 32#64) ↦₆₄ st2) ∗ ((s0.sp - 24#64) ↦₆₄ st3) ∗
        ((s0.sp - 16#64) ↦₆₄ st4) ∗ ((s0.sp - 8#64) ↦₆₄ st5) ∗
        vecHeader outPtr v0 v1 v2 ∗ rustStdVecBuf A 0 oldPtr bs ∗ A.pool lb lk s0 ∗
        errnoCell s0.tpidrEl0)
      post
      ((rustFinishGrowSpec A finishStack).onOom
        (outPtr, v0, v1, v2, 0, oldPtr, bs, newCap, lb, lk) s0) := by
  have hlayout : RustLayoutOk newCap 1 := ⟨hnew_pos, ⟨0, rfl⟩, by omega, by decide⟩
  have humulh : BitVec.setWidth 64 ((1#128 * BitVec.setWidth 128 (BitVec.ofNat 64 newCap)) >>> 64) = 0#64 :=
    umulh_one128_left_64 _
  have hmul1 : 1#64 * BitVec.ofNat 64 newCap = BitVec.ofNat 64 newCap := BitVec.one_mul _
  have hhi1 : (9223372036854775807#64).ult (BitVec.ofNat 64 newCap) = false := by
    simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : newCap < 2 ^ 64)]; omega
  have hhi2 : (BitVec.ofNat 64 newCap).ule 9223372036854775807#64 = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : newCap < 2 ^ 64)]; omega
  have hnc_ne0 : BitVec.ofNat 64 newCap ≠ 0#64 := by bv_omega
  have hnc_beq0 : (BitVec.ofNat 64 newCap == 0#64) = false := beq_false_of_ne hnc_ne0
  apply sepWP_seg_rebase_pure_alloc (lib := rustStdIoMultiLib) (mpl := RawVecGrowPlacement.mpl)
    hext 22 (by decide) rustIoBlockNoSvc0_22 hcl
    (mid := rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl rustNoAllocShimIoSym)
  intro s0' hcpu0; change SepWP (rvgPC22.rebase rvgPl22.base (fun _ => none)) _ _ _ _
  have hpc0' : s0'.pc = rvgPl22.base := hcpu0.toSameCpuState.pc_eq.trans hpc
  have hrun0' : s0'.status = .Running := hcpu0.toSameCpuState.status_eq.trans hrun
  have hsp0' : s0'.spAligned = true := hcpu0.toSameCpuState.spAligned.trans hsp
  have hx0' : s0'.readReg64 (.gpr 0#5) = outPtr := (hcpu0.toSameCpuState.readReg64 .x0).trans hx0
  have hx1' : s0'.readReg64 (.gpr 1#5) = 0#64 := (hcpu0.toSameCpuState.readReg64 .x1).trans hx1
  have hx3' : s0'.readReg64 (.gpr 3#5) = BitVec.ofNat 64 newCap :=
    (hcpu0.toSameCpuState.readReg64 .x3).trans hx3
  have hx4' : s0'.readReg64 (.gpr 4#5) = 1#64 := (hcpu0.toSameCpuState.readReg64 .x4).trans hx4
  have hx5' : s0'.readReg64 (.gpr 5#5) = 1#64 := (hcpu0.toSameCpuState.readReg64 .x5).trans hx5
  wp_conv_pre => simp only [← hcpu0.toSameCpuState.sp_eq]
  clear hpc; wp_sym_steps
  refine SepWP.done rvgShim_pc (by simpa [arm64_norm] using hrun0')
    fun sm1 hcpu_m1 hcl1 hnsp1 hsym1 => ?_
  obtain ⟨hpres_01, hpool_01⟩ := allocCallPreserved_of_seg hcpu0 hcpu_m1 hnsp1 hsym1
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq1 : A.pool lb lk s0 = A.pool lb lk sm1 := (A.pool_transport lb lk s0 sm1 hpool_01).symm
  have hhi_m1 : RvgHiCS s0 sm1 :=
    (RvgHiCS.refl s0).of_seg hcpu0 hcpu_m1 (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpc1 : sm1.pc = rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl rustNoAllocShimIoSym :=
    hcpu_m1.toSameCpuState.pc_eq.trans rvgShim_pc
  have hrun1 : sm1.status = .Running :=
    hcpu_m1.toSameCpuState.status_eq.trans (by simpa [arm64_norm] using hrun0')
  have hsp1_eq : sm1.sp = s0.sp - 48#64 := by
    rw [hcpu_m1.toSameCpuState.sp_eq]; simp [arm64_norm, hcpu0.toSameCpuState.sp_eq]
  have hsp1 : sm1.spAligned = true := by
    simp only [State.spAligned]; rw [hsp1_eq]; exact s0.spAligned_sub 48#64 hsp
  have hlr1 : sm1.readReg64 .lr = rvgPl22.base + 108#64 := by
    rw [hcpu_m1.toSameCpuState.readReg64 .lr]; simp [arm64_norm]
  refine SepWP.weaken_pre (P' :=
      Rust.hookFrame sm1.sp ∗
      memRegion (sm1.sp - BitVec.ofNat 64 finishStack) (finishStack - Rust.hookStack) ∗
      rvgSavedSlots22 s0 st3 ∗ vecHeader outPtr v0 v1 v2 ∗
      rustStdVecBuf A 0 oldPtr bs ∗ A.pool lb lk sm1 ∗ errnoCell s0.tpidrEl0)
    (by
      rw [stackAt_shrink (s0'.sp - 48#64) finishStack Rust.hookStack hstk.1 (by omega)]
      dsimp only [Rust.hookFrame, stackAt, rvgSavedSlots22]
      simp only [hcpu0.toSameCpuState.sp_eq, hcpu0.toSameCpuState.readReg64,
        hpool_eq1, hsp1_eq, bv_lin_norm]
      sep_entail) ?_
  apply seqCodeLoadedWhere hcl1 (mid := rvgPl22.base + 108#64)
  apply (SepWP.call_subroutine_frame hshim (x := ()) hpc1 hrun1 hsp1 hlr1
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'; dsimp only [rustAllocShimSpec]; exact Satisfies.mono (by sep_frame) hm'
  · intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1
    refine SepWP.done hpc_sf1 hrun_sf1 fun hcl_sf1 => ?_
    dsimp only [rustAllocShimSpec]; wp_conv_pre => simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hpres_1s, hbrk_1s⟩
    have hpool_1s : PoolPreserved sm1 sf1 := ⟨hpres_1s.2.2.2.2.1, hbrk_1s, hpres_1s.2.2.2.1⟩
    have hpres_0s : AllocCallPreserved s0 sf1 := allocCallPreserved_trans hpres_01 hpres_1s
    have hpool_0s : PoolPreserved s0 sf1 := poolPreserved_trans hpool_01 hpool_1s
    have hpool_eq_s : A.pool lb lk sm1 = A.pool lb lk sf1 :=
      (A.pool_transport lb lk sm1 sf1 hpool_1s).symm
    have hsp_sf1_eq : sf1.sp = s0.sp - 48#64 := hsp_sf1.trans hsp1_eq
    have hhi_sf1 : RvgHiCS s0 sf1 := hhi_m1.of_cs hcs_sf1
    have hx19_sf1 : sf1.readReg64 (.gpr 19#5) = outPtr := by
      rw [hcs_sf1.readReg64_x19, hcpu_m1.toSameCpuState.readReg64 (.gpr 19#5)]; simp [arm64_norm]
    have hx20_sf1 : sf1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 newCap := by
      rw [hcs_sf1.readReg64_x20, hcpu_m1.toSameCpuState.readReg64 (.gpr 20#5)]; simp [arm64_norm]
    have hx21_sf1 : sf1.readReg64 (.gpr 21#5) = 1#64 := by
      rw [hcs_sf1.readReg64_x21, hcpu_m1.toSameCpuState.readReg64 (.gpr 21#5)]; simp [arm64_norm]
    apply sepWP_seg_rebase_pure_alloc (lib := rustStdIoMultiLib) (mpl := RawVecGrowPlacement.mpl)
      hext 22 (by decide) rustIoBlockNoSvc0_22 hcl_sf1
      (mid := rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl rustAllocIoSym)
    intro s1' hcpu1; change SepWP (rvgPC22.rebase rvgPl22.base (fun _ => none)) _ _ _ _
    have hpc1' : s1'.pc = rvgPl22.base + 108#64 := hcpu1.toSameCpuState.pc_eq.trans hpc_sf1
    have hrun1' : s1'.status = .Running := hcpu1.toSameCpuState.status_eq.trans hrun_sf1
    have hsp1_in : s1'.sp = s0.sp - 48#64 := hcpu1.toSameCpuState.sp_eq.trans hsp_sf1_eq
    have hsp1' : s1'.spAligned = true := by
      simp only [State.spAligned]; rw [hsp1_in]; exact s0.spAligned_sub 48#64 hsp
    have hx20_1' : s1'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 newCap :=
      (hcpu1.toSameCpuState.readReg64 (.gpr 20#5)).trans hx20_sf1
    have hx21_1' : s1'.readReg64 (.gpr 21#5) = 1#64 :=
      (hcpu1.toSameCpuState.readReg64 (.gpr 21#5)).trans hx21_sf1
    wp_sym_steps
    refine SepWP.done rvgAlloc_pc (by simpa [arm64_norm] using hrun1')
      fun sm2 hcpu_m2 hcl2 hnsp2 hsym2 => ?_
    obtain ⟨hpres_s2, hpool_s2⟩ := allocCallPreserved_of_seg hcpu1 hcpu_m2 hnsp2 hsym2
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpres_02 : AllocCallPreserved s0 sm2 := allocCallPreserved_trans hpres_0s hpres_s2
    have hpool_02 : PoolPreserved s0 sm2 := poolPreserved_trans hpool_0s hpool_s2
    have hpool_eq2 : A.pool lb lk sf1 = A.pool lb lk sm2 :=
      (A.pool_transport lb lk sf1 sm2 hpool_s2).symm
    have hhi_m2 : RvgHiCS s0 sm2 :=
      hhi_sf1.of_seg hcpu1 hcpu_m2 (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpc2 : sm2.pc = rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl rustAllocIoSym :=
      hcpu_m2.toSameCpuState.pc_eq.trans rvgAlloc_pc
    have hrun2 : sm2.status = .Running :=
      hcpu_m2.toSameCpuState.status_eq.trans (by simpa [arm64_norm] using hrun1')
    have hsp2_eq : sm2.sp = s0.sp - 48#64 := by
      rw [hcpu_m2.toSameCpuState.sp_eq]; simp [arm64_norm, hsp1_in]
    have hsp2 : sm2.spAligned = true := by
      simp only [State.spAligned]; rw [hsp2_eq]; exact s0.spAligned_sub 48#64 hsp
    have hlr2 : sm2.readReg64 .lr = rvgPl22.base + 120#64 := by
      rw [hcpu_m2.toSameCpuState.readReg64 .lr]; simp [arm64_norm]
    have hx0_m2 : (sm2.readReg64 .x0).toNat = newCap := by
      rw [hcpu_m2.toSameCpuState.readReg64 .x0]; simp only [arm64_norm, BitVec.toNat_ofNat]; omega
    have hx1_m2 : (sm2.readReg64 .x1).toNat = 1 := by
      rw [hcpu_m2.toSameCpuState.readReg64 .x1]; simp [arm64_norm]
    wp_conv_pre => rw [hpool_eq_s, hpool_eq2, hsp1_eq, ← hsp2_eq, ← errnoCell_eq, ← hpool_02.2.2]
    apply seqCodeLoadedWhere hcl2 (mid := rvgPl22.base + 120#64)
    apply (SepWP.call_subroutine_frame halloc (x := (newCap, 1, lb, lk)) hpc2 hrun2 hsp2 hlr2
      (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
      (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (h_oom := fun R' sf _ ho => by
        dsimp only [rustStdAllocSpec] at ho; rw [satisfies_pure_sepConj] at ho
        dsimp only [rustFinishGrowSpec]; rw [satisfies_pure_sepConj]
        exact ⟨⟨hcap_lt, sm2, ⟨hpres_02.2.1, hpres_02.2.2.1⟩, hpres_02.1, hpool_02, ho.1⟩,
          Satisfies.drop_left ho.2⟩))
    · intro R' hm'; dsimp only [rustStdAllocSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_m2, hx1_m2, hlayout, hcan⟩, Satisfies.mono (by sep_frame) hm'⟩
    · intro sf2 hpc_sf2 hrun_sf2 hsp_sf2 hcs_sf2
      refine SepWP.done hpc_sf2 hrun_sf2 fun hcl_sf2 => ?_
      dsimp only [rustStdAllocSpec]
      wp_conv_pre => simp only [sepConj_assoc, hsp2_eq, hpool_02.2.2, errnoCell_eq]
      apply SepWP.pure_elim; intro hpres_2a
      have hpres_0a : AllocCallPreserved s0 sf2 := allocCallPreserved_trans hpres_02 hpres_2a
      have hsp_sf2_eq : sf2.sp = s0.sp - 48#64 := hsp_sf2.trans hsp2_eq
      have hhi_sf2 : RvgHiCS s0 sf2 := hhi_m2.of_cs hcs_sf2
      have hx19_sf2 : sf2.readReg64 (.gpr 19#5) = outPtr := by
        rw [hcs_sf2.readReg64_x19, hcpu_m2.toSameCpuState.readReg64 (.gpr 19#5)]; simp only [arm64_norm]
        exact (hcpu1.toSameCpuState.readReg64 (.gpr 19#5)).trans hx19_sf1
      have hx20_sf2 : sf2.readReg64 (.gpr 20#5) = BitVec.ofNat 64 newCap := by
        rw [hcs_sf2.readReg64_x20, hcpu_m2.toSameCpuState.readReg64 (.gpr 20#5)]; simp only [arm64_norm]
        exact hx20_1'
      have hx21_sf2 : sf2.readReg64 (.gpr 21#5) = 1#64 := by
        rw [hcs_sf2.readReg64_x21, hcpu_m2.toSameCpuState.readReg64 (.gpr 21#5)]; simp only [arm64_norm]
        exact hx21_1'
      by_cases hnull : sf2.readReg64 .x0 = 0#64
      · have hnull0 : sf2.readReg64 .x0 = 0 := hnull
        wp_conv_pre => simp only [hnull0, ↓reduceIte, sepConj_assoc]
        refine SepWP.weaken_pre (P' :=
            ⌜NullAllowed newCap 1⌝ ∗
            (stackAt (s0.sp - 48#64) finishStack ∗ rvgSavedSlots22 s0 st3 ∗
              vecHeader outPtr v0 v1 v2 ∗ rustStdVecBuf A 0 oldPtr bs ∗ A.pool lb lk sf2 ∗
              errnoCell s0.tpidrEl0))
          (by
            rw [stackAt_shrink (s0.sp - 48#64) finishStack Rust.hookStack hstk.1 (by omega)]
            dsimp only [Rust.hookFrame, stackAt]; sep_entail) ?_
        apply SepWP.pure_elim; intro hnull_ok
        apply sepWP_seg_rebase_pure_alloc (lib := rustStdIoMultiLib) (mpl := RawVecGrowPlacement.mpl)
          hext 22 (by decide) rustIoBlockNoSvc0_22 hcl_sf2 (mid := rvgPl22.base + 124#64)
        intro s2' hcpu2; change SepWP (rvgPC22.rebase rvgPl22.base (fun _ => none)) _ _ _ _
        have hpc2' : s2'.pc = rvgPl22.base + 120#64 := hcpu2.toSameCpuState.pc_eq.trans hpc_sf2
        have hrun2' : s2'.status = .Running := hcpu2.toSameCpuState.status_eq.trans hrun_sf2
        have hx0_2' : s2'.readReg64 (.gpr 0#5) = 0#64 := (hcpu2.toSameCpuState.readReg64 .x0).trans hnull
        wp_sym_steps
        refine SepWP.done (by rfl) (by simpa [arm64_norm] using hrun2')
          fun s_ep hcpu_ep hcl_ep hnsp_ep hsym_ep => ?_
        obtain ⟨hpres_aep, hpool_aep⟩ := allocCallPreserved_of_seg hcpu2 hcpu_ep hnsp_ep hsym_ep
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpool_eq_ep : A.pool lb lk sf2 = A.pool lb lk s_ep :=
          (A.pool_transport lb lk sf2 s_ep hpool_aep).symm
        refine SepWP.weaken_pre (by rw [hpool_eq_ep]; sep_entail) <|
          rustFinishGrow_epilogue_err A hext hstk.2 hcl_ep
            (by rw [hcpu_ep.toSameCpuState.pc_eq]; rfl)
            (hcpu_ep.toSameCpuState.status_eq.trans hrun2') hsp
            ((hcpu_ep.toSameCpuState.sp_eq.trans (by simp [arm64_norm])).trans
              (hcpu2.toSameCpuState.sp_eq.trans hsp_sf2_eq))
            (by rw [hcpu_ep.toSameCpuState.readReg64 (.gpr 19#5)]; simp only [arm64_norm]; exact (hcpu2.toSameCpuState.readReg64 (.gpr 19#5)).trans hx19_sf2)
            (by rw [hcpu_ep.toSameCpuState.readReg64 (.gpr 20#5)]; simp only [arm64_norm]; exact (hcpu2.toSameCpuState.readReg64 (.gpr 20#5)).trans hx20_sf2)
            (by rw [hcpu_ep.toSameCpuState.readReg64 (.gpr 21#5)]; simp only [arm64_norm]; exact (hcpu2.toSameCpuState.readReg64 (.gpr 21#5)).trans hx21_sf2)
            (hhi_sf2.of_seg hcpu2 hcpu_ep (by simp [arm64_norm]) (by simp [arm64_norm])
              (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
              (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
            (allocCallPreserved_trans hpres_0a hpres_aep) hnull_ok hcont
      · have hnull0 : ¬ sf2.readReg64 .x0 = 0 := hnull
        have hbs_nil : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
        wp_conv_pre => simp only [hnull0, ↓reduceIte, sepConj_assoc]
        refine SepWP.weaken_pre (P' :=
            stackAt (s0.sp - 48#64) finishStack ∗ rvgSavedSlots22 s0 st3 ∗
            vecHeader outPtr v0 v1 v2 ∗ rustStdVecBuf A newCap (sf2.readReg64 .x0) bs ∗
            A.pool (rustVecGrowLb A lb 0 newCap) (rustVecGrowLk lk 0) sf2 ∗
            errnoCell s0.tpidrEl0)
          (by
            subst hbs_nil
            rw [stackAt_shrink (s0.sp - 48#64) finishStack Rust.hookStack hstk.1 (by omega)]
            dsimp only [Rust.hookFrame, stackAt, rustStdVecBuf, rustVecGrowLb, rustVecGrowLk]
            simp only [Nat.ne_of_gt hnew_pos, ↓reduceIte, List.length_nil, Nat.sub_zero,
              pointsToBytes_nil, Nat.mod_one, pure_true, emp_sepConj, sepConj_emp, bv_lin_norm]
            have hp0 : (⌜0 ≤ 0 ∧ 0 < 2 ^ 63 ∧ oldPtr ≠ 0⌝ : SepProp) = emp := by simp [hold_nz]
            have hp1 : (⌜0 ≤ newCap ∧ newCap < 2 ^ 63 ∧ sf2.readReg64 .x0 ≠ 0⌝ : SepProp) = emp := by
              simp [hcap_lt, hnull]
            rw [hp0, hp1, sepConj_emp, emp_sepConj]
            sep_entail) ?_
        have hx0_beq0 : (sf2.readReg64 (.gpr 0#5) == 0#64) = false := beq_false_of_ne hnull
        have hx0_bne0 : (sf2.readReg64 (.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hnull
        apply sepWP_seg_rebase_pure_alloc (lib := rustStdIoMultiLib) (mpl := RawVecGrowPlacement.mpl)
          hext 22 (by decide) rustIoBlockNoSvc0_22 hcl_sf2 (mid := rvgPl22.base + 140#64)
        intro s2' hcpu2; change SepWP (rvgPC22.rebase rvgPl22.base (fun _ => none)) _ _ _ _
        have hpc2' : s2'.pc = rvgPl22.base + 120#64 := hcpu2.toSameCpuState.pc_eq.trans hpc_sf2
        have hrun2' : s2'.status = .Running := hcpu2.toSameCpuState.status_eq.trans hrun_sf2
        have hx0_2' : s2'.readReg64 (.gpr 0#5) = sf2.readReg64 (.gpr 0#5) :=
          hcpu2.toSameCpuState.readReg64 .x0
        wp_sym_steps
        refine SepWP.done (by rfl) (by simpa [arm64_norm] using hrun2')
          fun s_ep hcpu_ep hcl_ep hnsp_ep hsym_ep => ?_
        obtain ⟨hpres_aep, hpool_aep⟩ := allocCallPreserved_of_seg hcpu2 hcpu_ep hnsp_ep hsym_ep
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpool_eq_ep :
            A.pool (rustVecGrowLb A lb 0 newCap) (rustVecGrowLk lk 0) sf2 =
              A.pool (rustVecGrowLb A lb 0 newCap) (rustVecGrowLk lk 0) s_ep :=
          (A.pool_transport _ _ sf2 s_ep hpool_aep).symm
        refine SepWP.weaken_pre (by rw [hpool_eq_ep]; sep_entail) <|
          rustFinishGrow_epilogue_ok A hext hstk.2 hcl_ep
            (by rw [hcpu_ep.toSameCpuState.pc_eq]; rfl)
            (hcpu_ep.toSameCpuState.status_eq.trans hrun2') hsp
            ((hcpu_ep.toSameCpuState.sp_eq.trans (by simp [arm64_norm])).trans
              (hcpu2.toSameCpuState.sp_eq.trans hsp_sf2_eq))
            (by rw [hcpu_ep.toSameCpuState.readReg64 .x0]; simp only [arm64_norm]; exact hcpu2.toSameCpuState.readReg64 .x0)
            (by rw [hcpu_ep.toSameCpuState.readReg64 (.gpr 19#5)]; simp only [arm64_norm]; exact (hcpu2.toSameCpuState.readReg64 (.gpr 19#5)).trans hx19_sf2)
            (by rw [hcpu_ep.toSameCpuState.readReg64 (.gpr 20#5)]; simp only [arm64_norm]; exact (hcpu2.toSameCpuState.readReg64 (.gpr 20#5)).trans hx20_sf2)
            (hhi_sf2.of_seg hcpu2 hcpu_ep (by simp [arm64_norm]) (by simp [arm64_norm])
              (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
              (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
            (allocCallPreserved_trans hpres_0a hpres_aep) hcap_lt hcont

private theorem rustFinishGrow_pos_cap [RawVecGrowPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext : ∀ pc, P.externAt? pc = none)
    {s0 : State} {outPtr v0 v1 v2 oldPtr st0 st1 st2 st3 st4 st5 : BitVec 64}
    {oldCap newCap lb lk finishStack : Nat} {bs : List (BitVec 8)}
    {post : State → SepProp → Prop}
    (hstk : Rust.hookStack ≤ finishStack ∧ 48 + finishStack ≤ 2 ^ 64)
    (hrealloc : subroutine_ok P
      (rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl rustReallocIoSym) (rustStdReallocSpec A))
    (hcl : rustStdIoMultiLib.CodeLoadedWhere (· == 22) RawVecGrowPlacement.mpl s0.mem)
    (hpc : s0.pc = rvgPl22.base) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = outPtr) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 oldCap)
    (hx2 : s0.readReg64 .x2 = oldPtr) (hx3 : s0.readReg64 .x3 = BitVec.ofNat 64 newCap)
    (hx4 : s0.readReg64 .x4 = 1#64) (hx5 : s0.readReg64 .x5 = 1#64)
    (hold_pos : 0 < oldCap) (hold_lt : oldCap < 2 ^ 63) (hold_nz : oldPtr ≠ 0#64)
    (hnew_pos : 0 < newCap) (hcap_lt : newCap < 2 ^ 63)
    (hbs_old : bs.length ≤ oldCap) (hbs_new : bs.length ≤ newCap)
    (hcan : A.CanAlloc lb lk newCap 1)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      post sf ((rustFinishGrowSpec A finishStack).post
        (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, lb, lk) s0 sf)) :
    SepWP P (s0.readReg64 .lr) s0
      (stackAt (s0.sp - 48#64) finishStack ∗
        ((s0.sp - 48#64) ↦₆₄ st0) ∗ ((s0.sp - 40#64) ↦₆₄ st1) ∗
        ((s0.sp - 32#64) ↦₆₄ st2) ∗ ((s0.sp - 24#64) ↦₆₄ st3) ∗
        ((s0.sp - 16#64) ↦₆₄ st4) ∗ ((s0.sp - 8#64) ↦₆₄ st5) ∗
        vecHeader outPtr v0 v1 v2 ∗ rustStdVecBuf A oldCap oldPtr bs ∗ A.pool lb lk s0 ∗
        errnoCell s0.tpidrEl0)
      post
      ((rustFinishGrowSpec A finishStack).onOom
        (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, lb, lk) s0) := by
  have hlayout : RustLayoutOk newCap 1 := ⟨hnew_pos, ⟨0, rfl⟩, by omega, by decide⟩
  have humulh : BitVec.setWidth 64 ((1#128 * BitVec.setWidth 128 (BitVec.ofNat 64 newCap)) >>> 64) = 0#64 :=
    umulh_one128_left_64 _
  have hmul1 : 1#64 * BitVec.ofNat 64 newCap = BitVec.ofNat 64 newCap := BitVec.one_mul _
  have hmul1_old : 1#64 * BitVec.ofNat 64 oldCap = BitVec.ofNat 64 oldCap := BitVec.one_mul _
  have hhi1 : (9223372036854775807#64).ult (BitVec.ofNat 64 newCap) = false := by
    simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : newCap < 2 ^ 64)]; omega
  have hhi2 : (BitVec.ofNat 64 newCap).ule 9223372036854775807#64 = true := by
    simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : newCap < 2 ^ 64)]; omega
  have hold_ne0 : BitVec.ofNat 64 oldCap ≠ 0#64 := by bv_omega
  have hold_beq0 : (BitVec.ofNat 64 oldCap == 0#64) = false := beq_false_of_ne hold_ne0
  apply sepWP_seg_rebase_pure_alloc (lib := rustStdIoMultiLib) (mpl := RawVecGrowPlacement.mpl)
    hext 22 (by decide) rustIoBlockNoSvc0_22 hcl
    (mid := rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl rustReallocIoSym)
  intro s0' hcpu0; change SepWP (rvgPC22.rebase rvgPl22.base (fun _ => none)) _ _ _ _
  have hpc0' : s0'.pc = rvgPl22.base := hcpu0.toSameCpuState.pc_eq.trans hpc
  have hrun0' : s0'.status = .Running := hcpu0.toSameCpuState.status_eq.trans hrun
  have hsp0' : s0'.spAligned = true := hcpu0.toSameCpuState.spAligned.trans hsp
  have hx0' : s0'.readReg64 (.gpr 0#5) = outPtr := (hcpu0.toSameCpuState.readReg64 .x0).trans hx0
  have hx1' : s0'.readReg64 (.gpr 1#5) = BitVec.ofNat 64 oldCap :=
    (hcpu0.toSameCpuState.readReg64 .x1).trans hx1
  have hx2' : s0'.readReg64 (.gpr 2#5) = oldPtr := (hcpu0.toSameCpuState.readReg64 .x2).trans hx2
  have hx3' : s0'.readReg64 (.gpr 3#5) = BitVec.ofNat 64 newCap :=
    (hcpu0.toSameCpuState.readReg64 .x3).trans hx3
  have hx4' : s0'.readReg64 (.gpr 4#5) = 1#64 := (hcpu0.toSameCpuState.readReg64 .x4).trans hx4
  have hx5' : s0'.readReg64 (.gpr 5#5) = 1#64 := (hcpu0.toSameCpuState.readReg64 .x5).trans hx5
  wp_conv_pre => simp only [← hcpu0.toSameCpuState.sp_eq]
  clear hpc; wp_sym_steps
  refine SepWP.done rvgRealloc_pc (by simpa [arm64_norm] using hrun0')
    fun sm1 hcpu_m1 hcl1 hnsp1 hsym1 => ?_
  obtain ⟨hpres_01, hpool_01⟩ := allocCallPreserved_of_seg hcpu0 hcpu_m1 hnsp1 hsym1
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq1 : A.pool lb lk s0 = A.pool lb lk sm1 := (A.pool_transport lb lk s0 sm1 hpool_01).symm
  have hhi_m1 : RvgHiCS s0 sm1 :=
    (RvgHiCS.refl s0).of_seg hcpu0 hcpu_m1 (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpc1 : sm1.pc = rustStdIoMultiLib.resolve RawVecGrowPlacement.mpl rustReallocIoSym :=
    hcpu_m1.toSameCpuState.pc_eq.trans rvgRealloc_pc
  have hrun1 : sm1.status = .Running :=
    hcpu_m1.toSameCpuState.status_eq.trans (by simpa [arm64_norm] using hrun0')
  have hsp1_eq : sm1.sp = s0.sp - 48#64 := by
    rw [hcpu_m1.toSameCpuState.sp_eq]; simp [arm64_norm, hcpu0.toSameCpuState.sp_eq]
  have hsp1 : sm1.spAligned = true := by
    simp only [State.spAligned]; rw [hsp1_eq]; exact s0.spAligned_sub 48#64 hsp
  have hlr1 : sm1.readReg64 .lr = rvgPl22.base + 92#64 := by
    rw [hcpu_m1.toSameCpuState.readReg64 .lr]; simp [arm64_norm]
  have hx0_m1 : sm1.readReg64 .x0 = oldPtr := by
    rw [hcpu_m1.toSameCpuState.readReg64 .x0]; simp [arm64_norm]
  have hx1_m1 : (sm1.readReg64 .x1).toNat = oldCap := by
    rw [hcpu_m1.toSameCpuState.readReg64 .x1]; simp only [arm64_norm, hmul1_old, BitVec.toNat_ofNat]; omega
  have hx2_m1 : (sm1.readReg64 .x2).toNat = 1 := by
    rw [hcpu_m1.toSameCpuState.readReg64 .x2]; simp [arm64_norm]
  have hx3_m1 : (sm1.readReg64 .x3).toNat = newCap := by
    rw [hcpu_m1.toSameCpuState.readReg64 .x3]; simp only [arm64_norm, BitVec.toNat_ofNat]; omega
  refine SepWP.weaken_pre (P' :=
      Rust.hookFrame sm1.sp ∗
      memRegion (sm1.sp - BitVec.ofNat 64 finishStack) (finishStack - Rust.hookStack) ∗
      rvgSavedSlots22 s0 st3 ∗ vecHeader outPtr v0 v1 v2 ∗
      A.pool lb lk sm1 ∗ A.live oldPtr oldCap 1 ∗ (oldPtr ↦ₛ bs) ∗
      memRegion (oldPtr + BitVec.ofNat 64 bs.length) (oldCap - bs.length) ∗
      StdErrnoCell sm1.tpidrEl0)
    (by
      rw [← errnoCell_eq, ← hpool_01.2.2,
          stackAt_shrink (s0'.sp - 48#64) finishStack Rust.hookStack hstk.1 (by omega)]
      dsimp only [Rust.hookFrame, stackAt, rvgSavedSlots22, rustStdVecBuf]
      simp only [Nat.ne_of_gt hold_pos, ↓reduceIte,
        hcpu0.toSameCpuState.sp_eq, hcpu0.toSameCpuState.readReg64, hpool_eq1, hsp1_eq, bv_lin_norm]
      have hp_old : (⌜bs.length ≤ oldCap ∧ oldCap < 2 ^ 63 ∧ oldPtr ≠ 0⌝ : SepProp) = emp := by
        simp [hbs_old, hold_lt, hold_nz]
      rw [hp_old, emp_sepConj]; sep_entail) ?_
  apply seqCodeLoadedWhere hcl1 (mid := rvgPl22.base + 92#64)
  apply (SepWP.call_subroutine_frame hrealloc
    (x := (oldPtr, oldCap, 1, newCap, bs, lb, lk)) hpc1 hrun1 hsp1 hlr1
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun R' sf _ ho => by
      dsimp only [rustStdReallocSpec] at ho; rw [satisfies_pure_sepConj] at ho
      dsimp only [rustFinishGrowSpec]; rw [satisfies_pure_sepConj]
      exact ⟨⟨hcap_lt, sm1, ⟨hpres_01.2.1, hpres_01.2.2.1⟩, hpres_01.1, hpool_01, ho.1⟩,
        Satisfies.drop_left ho.2⟩))
  · intro R' hm'; dsimp only [rustStdReallocSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_m1, hx1_m1, hx2_m1, hx3_m1, hlayout, hbs_old, hbs_new, hcan⟩,
      Satisfies.mono (by sep_frame) hm'⟩
  · intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1
    refine SepWP.done hpc_sf1 hrun_sf1 fun hcl_sf1 => ?_
    dsimp only [rustStdReallocSpec]
    wp_conv_pre => simp only [sepConj_assoc, hsp1_eq, hpool_01.2.2, errnoCell_eq]
    apply SepWP.pure_elim; intro hpres_1r
    have hpres_0r : AllocCallPreserved s0 sf1 := allocCallPreserved_trans hpres_01 hpres_1r
    have hsp_sf1_eq : sf1.sp = s0.sp - 48#64 := hsp_sf1.trans hsp1_eq
    have hhi_sf1 : RvgHiCS s0 sf1 := hhi_m1.of_cs hcs_sf1
    have hx19_sf1 : sf1.readReg64 (.gpr 19#5) = outPtr := by
      rw [hcs_sf1.readReg64_x19, hcpu_m1.toSameCpuState.readReg64 (.gpr 19#5)]; simp [arm64_norm]
    have hx20_sf1 : sf1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 newCap := by
      rw [hcs_sf1.readReg64_x20, hcpu_m1.toSameCpuState.readReg64 (.gpr 20#5)]; simp [arm64_norm]
    have hx21_sf1 : sf1.readReg64 (.gpr 21#5) = 1#64 := by
      rw [hcs_sf1.readReg64_x21, hcpu_m1.toSameCpuState.readReg64 (.gpr 21#5)]; simp [arm64_norm]
    by_cases hnull : sf1.readReg64 .x0 = 0#64
    · have hnull0 : sf1.readReg64 .x0 = 0 := hnull
      wp_conv_pre => simp only [hnull0, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre (P' :=
          ⌜NullAllowed newCap 1⌝ ∗
          (stackAt (s0.sp - 48#64) finishStack ∗ rvgSavedSlots22 s0 st3 ∗
            vecHeader outPtr v0 v1 v2 ∗ rustStdVecBuf A oldCap oldPtr bs ∗ A.pool lb lk sf1 ∗
            errnoCell s0.tpidrEl0))
        (by
          rw [stackAt_shrink (s0.sp - 48#64) finishStack Rust.hookStack hstk.1 (by omega)]
          dsimp only [Rust.hookFrame, stackAt, rustStdVecBuf]
          simp only [Nat.ne_of_gt hold_pos, ↓reduceIte]
          rw [pure_sepConj_of_true (φ := bs.length ≤ oldCap ∧ oldCap < 2 ^ 63 ∧ oldPtr ≠ 0#64)
                ⟨hbs_old, hold_lt, hold_nz⟩]
          sep_entail) ?_
      apply SepWP.pure_elim; intro hnull_ok
      apply sepWP_seg_rebase_pure_alloc (lib := rustStdIoMultiLib) (mpl := RawVecGrowPlacement.mpl)
        hext 22 (by decide) rustIoBlockNoSvc0_22 hcl_sf1 (mid := rvgPl22.base + 124#64)
      intro s2' hcpu2; change SepWP (rvgPC22.rebase rvgPl22.base (fun _ => none)) _ _ _ _
      have hpc2' : s2'.pc = rvgPl22.base + 92#64 := hcpu2.toSameCpuState.pc_eq.trans hpc_sf1
      have hrun2' : s2'.status = .Running := hcpu2.toSameCpuState.status_eq.trans hrun_sf1
      have hx0_2' : s2'.readReg64 (.gpr 0#5) = 0#64 := (hcpu2.toSameCpuState.readReg64 .x0).trans hnull
      wp_sym_steps
      refine SepWP.done (by rfl) (by simpa [arm64_norm] using hrun2')
        fun s_ep hcpu_ep hcl_ep hnsp_ep hsym_ep => ?_
      obtain ⟨hpres_rep, hpool_rep⟩ := allocCallPreserved_of_seg hcpu2 hcpu_ep hnsp_ep hsym_ep
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_ep : A.pool lb lk sf1 = A.pool lb lk s_ep :=
        (A.pool_transport lb lk sf1 s_ep hpool_rep).symm
      refine SepWP.weaken_pre (by rw [hpool_eq_ep]; sep_entail) <|
        rustFinishGrow_epilogue_err A hext hstk.2 hcl_ep
          (by rw [hcpu_ep.toSameCpuState.pc_eq]; rfl)
          (hcpu_ep.toSameCpuState.status_eq.trans hrun2') hsp
          ((hcpu_ep.toSameCpuState.sp_eq.trans (by simp [arm64_norm])).trans
            (hcpu2.toSameCpuState.sp_eq.trans hsp_sf1_eq))
          (by rw [hcpu_ep.toSameCpuState.readReg64 (.gpr 19#5)]; simp only [arm64_norm]; exact (hcpu2.toSameCpuState.readReg64 (.gpr 19#5)).trans hx19_sf1)
          (by rw [hcpu_ep.toSameCpuState.readReg64 (.gpr 20#5)]; simp only [arm64_norm]; exact (hcpu2.toSameCpuState.readReg64 (.gpr 20#5)).trans hx20_sf1)
          (by rw [hcpu_ep.toSameCpuState.readReg64 (.gpr 21#5)]; simp only [arm64_norm]; exact (hcpu2.toSameCpuState.readReg64 (.gpr 21#5)).trans hx21_sf1)
          (hhi_sf1.of_seg hcpu2 hcpu_ep (by simp [arm64_norm]) (by simp [arm64_norm])
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
          (allocCallPreserved_trans hpres_0r hpres_rep) hnull_ok hcont
    · have hnull0 : ¬ sf1.readReg64 .x0 = 0 := hnull
      wp_conv_pre => simp only [hnull0, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre (P' :=
          stackAt (s0.sp - 48#64) finishStack ∗ rvgSavedSlots22 s0 st3 ∗
          vecHeader outPtr v0 v1 v2 ∗ rustStdVecBuf A newCap (sf1.readReg64 .x0) bs ∗
          A.pool (rustVecGrowLb A lb oldCap newCap) (rustVecGrowLk lk oldCap) sf1 ∗
          errnoCell s0.tpidrEl0)
        (by
          rw [stackAt_shrink (s0.sp - 48#64) finishStack Rust.hookStack hstk.1 (by omega)]
          dsimp only [Rust.hookFrame, stackAt, rustStdVecBuf, rustVecGrowLb, rustVecGrowLk]
          simp only [Nat.ne_of_gt hold_pos, Nat.ne_of_gt hnew_pos, ↓reduceIte,
            Nat.mod_one, pure_true, emp_sepConj, bv_lin_norm]
          have hp_new : (⌜bs.length ≤ newCap ∧ newCap < 2 ^ 63 ∧ sf1.readReg64 .x0 ≠ 0⌝ : SepProp) = emp := by
            simp [hbs_new, hcap_lt, hnull]
          rw [hp_new, emp_sepConj]; sep_entail) ?_
      have hx0_beq0 : (sf1.readReg64 (.gpr 0#5) == 0#64) = false := beq_false_of_ne hnull
      have hx0_bne0 : (sf1.readReg64 (.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hnull
      apply sepWP_seg_rebase_pure_alloc (lib := rustStdIoMultiLib) (mpl := RawVecGrowPlacement.mpl)
        hext 22 (by decide) rustIoBlockNoSvc0_22 hcl_sf1 (mid := rvgPl22.base + 140#64)
      intro s2' hcpu2; change SepWP (rvgPC22.rebase rvgPl22.base (fun _ => none)) _ _ _ _
      have hpc2' : s2'.pc = rvgPl22.base + 92#64 := hcpu2.toSameCpuState.pc_eq.trans hpc_sf1
      have hrun2' : s2'.status = .Running := hcpu2.toSameCpuState.status_eq.trans hrun_sf1
      have hx0_2' : s2'.readReg64 (.gpr 0#5) = sf1.readReg64 (.gpr 0#5) :=
        hcpu2.toSameCpuState.readReg64 .x0
      wp_sym_steps
      refine SepWP.done (by rfl) (by simpa [arm64_norm] using hrun2')
        fun s_ep hcpu_ep hcl_ep hnsp_ep hsym_ep => ?_
      obtain ⟨hpres_rep, hpool_rep⟩ := allocCallPreserved_of_seg hcpu2 hcpu_ep hnsp_ep hsym_ep
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_ep :
          A.pool (rustVecGrowLb A lb oldCap newCap) (rustVecGrowLk lk oldCap) sf1 =
            A.pool (rustVecGrowLb A lb oldCap newCap) (rustVecGrowLk lk oldCap) s_ep :=
        (A.pool_transport _ _ sf1 s_ep hpool_rep).symm
      refine SepWP.weaken_pre (by rw [hpool_eq_ep]; sep_entail) <|
        rustFinishGrow_epilogue_ok A hext hstk.2 hcl_ep
          (by rw [hcpu_ep.toSameCpuState.pc_eq]; rfl)
          (hcpu_ep.toSameCpuState.status_eq.trans hrun2') hsp
          ((hcpu_ep.toSameCpuState.sp_eq.trans (by simp [arm64_norm])).trans
            (hcpu2.toSameCpuState.sp_eq.trans hsp_sf1_eq))
          (by rw [hcpu_ep.toSameCpuState.readReg64 .x0]; simp only [arm64_norm]; exact hcpu2.toSameCpuState.readReg64 .x0)
          (by rw [hcpu_ep.toSameCpuState.readReg64 (.gpr 19#5)]; simp only [arm64_norm]; exact (hcpu2.toSameCpuState.readReg64 (.gpr 19#5)).trans hx19_sf1)
          (by rw [hcpu_ep.toSameCpuState.readReg64 (.gpr 20#5)]; simp only [arm64_norm]; exact (hcpu2.toSameCpuState.readReg64 (.gpr 20#5)).trans hx20_sf1)
          (hhi_sf1.of_seg hcpu2 hcpu_ep (by simp [arm64_norm]) (by simp [arm64_norm])
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
          (allocCallPreserved_trans hpres_0r hpres_rep) hcap_lt hcont

/-- Block-subset (`CodeLoadedWhere keep`) correctness of `<alloc::raw_vec::RawVecInner>::finish_grow`
    (block `22` of `rustStdIoMultiLib`) over any `(A : RustStdAlloc oom)`. -/
theorem rustFinishGrow_okWhere {oom : State → State → Prop} (A : RustStdAlloc oom)
    {keep : Nat → Bool} {mpl : MultiPlacement} (hpl : rustStdIoMultiLib.Placeable mpl)
    {P : Program} {finishStack : Nat}
    (hext : ∀ pc, P.externAt? pc = none)
    (hk22 : keep 22 = true := by decide)
    (hstk : Rust.hookStack ≤ finishStack ∧ 48 + finishStack ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustNoAllocShimIoSym)
      rustAllocShimSpec)
    (halloc : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustAllocIoSym)
      (rustStdAllocSpec A))
    (hrealloc : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustReallocIoSym)
      (rustStdReallocSpec A)) :
    subroutine_ok P (rustStdIoMultiLib.resolve mpl finishGrowIoSym)
      (rustStdIoMultiLib.withCodeLoadedWhere keep mpl (rustFinishGrowSpec A finishStack)) := by
  letI : RawVecGrowPlacement := ⟨mpl, hpl⟩
  apply subroutine_ok_of_sepWP_init
  rintro ⟨outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, lb, lk⟩ R s0 hpc hrun hpre hsp
  rw [resolve_eq_base hpl 22 finishGrowIoSym (by decide) (by decide)] at hpc
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, rustFinishGrowSpec] at hpre ⊢
  rw [errnoCell_eq] at hpre
  rw [sepConj_comm _ ⌜rustStdIoMultiLib.CodeLoadedWhere keep mpl s0.mem⌝,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl_keep, hpre⟩
  have hcl : rustStdIoMultiLib.CodeLoadedWhere (· == 22) mpl s0.mem :=
    fun i _ hi => by rw [beq_iff_eq.mp hi] at *; exact hcl_keep 22 (by decide) hk22
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hnew_pos, hnew_lt64, hbs_new, hcan_imp⟩, hpre⟩
  have ⟨hbs_old, hold_lt, hold_nz⟩ :=
    satisfies_rustStdVecBuf_bounds_rvg (A := A) (cap := oldCap) (ptr := oldPtr) (bs := bs)
      (Satisfies.mono (by sep_frame) hpre)
  rw [show 48 + finishStack = finishStack + 8 * 6 by omega,
      stackAt_split_cells s0.sp finishStack 6 (by omega)] at hpre
  dsimp only [cells] at hpre
  simp only [Nat.reduceMul, bv_lin_norm, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨st0, st1, st2, st3, st4, st5, hpre⟩
  refine ⟨_, hpre, ?_⟩
  wp_conv_pre => simp only [sepConj_assoc]
  by_cases hcap_lt : newCap < 2 ^ 63
  · rcases Nat.eq_zero_or_pos oldCap with rfl | hold_pos
    · exact rustFinishGrow_zero_cap A hext hstk hshim halloc hcl hpc hrun hsp
        hx0 (by simpa using hx1) hx3 hx4 hx5 hold_nz hnew_pos hcap_lt hbs_old (hcan_imp hcap_lt)
        (post := fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (rustFinishGrowSpec A finishStack).post
              (outPtr, v0, v1, v2, 0, oldPtr, bs, newCap, lb, lk) s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf _ _ hsp_f hcs_f => ⟨fun hm_f => hm_f, hsp_f, hcs_f⟩)
    · exact rustFinishGrow_pos_cap A hext hstk hrealloc hcl hpc hrun hsp
        hx0 hx1 hx2 hx3 hx4 hx5 hold_pos hold_lt hold_nz hnew_pos hcap_lt hbs_old hbs_new
        (hcan_imp hcap_lt)
        (post := fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (rustFinishGrowSpec A finishStack).post
              (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, lb, lk) s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf _ _ hsp_f hcs_f => ⟨fun hm_f => hm_f, hsp_f, hcs_f⟩)
  · have humulh : BitVec.setWidth 64 ((1#128 * BitVec.setWidth 128 (BitVec.ofNat 64 newCap)) >>> 64) = 0#64 :=
      umulh_one128_left_64 _
    have hmul1 : 1#64 * BitVec.ofNat 64 newCap = BitVec.ofNat 64 newCap := BitVec.one_mul _
    have hhi1 : (9223372036854775807#64).ult (BitVec.ofNat 64 newCap) = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew_lt64]; omega
    have hhi2 : (BitVec.ofNat 64 newCap).ule 9223372036854775807#64 = false := by
      simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew_lt64]; omega
    have hnull : NullAllowed newCap 1 := by unfold NullAllowed; omega
    apply sepWP_seg_rebase_pure_alloc (lib := rustStdIoMultiLib) (mpl := RawVecGrowPlacement.mpl)
      hext 22 (by decide) rustIoBlockNoSvc0_22 hcl (mid := s0.readReg64 .lr)
    intro s0' hcpu0; change SepWP (rvgPC22.rebase rvgPl22.base (fun _ => none)) _ _ _ _
    have hpc0' : s0'.pc = rvgPl22.base := hcpu0.toSameCpuState.pc_eq.trans hpc
    have hrun0' : s0'.status = .Running := hcpu0.toSameCpuState.status_eq.trans hrun
    have hsp0' : s0'.spAligned = true := hcpu0.toSameCpuState.spAligned.trans hsp
    have hx0' : s0'.readReg64 (.gpr 0#5) = outPtr := (hcpu0.toSameCpuState.readReg64 .x0).trans hx0
    have hx3' : s0'.readReg64 (.gpr 3#5) = BitVec.ofNat 64 newCap :=
      (hcpu0.toSameCpuState.readReg64 .x3).trans hx3
    have hx4' : s0'.readReg64 (.gpr 4#5) = 1#64 := (hcpu0.toSameCpuState.readReg64 .x4).trans hx4
    have hx5' : s0'.readReg64 (.gpr 5#5) = 1#64 := (hcpu0.toSameCpuState.readReg64 .x5).trans hx5
    wp_conv_pre => simp only [vecHeader, ← hcpu0.toSameCpuState.sp_eq]
    clear hpc; wp_sym_steps
    refine SepWP.done (by simpa [arm64_norm] using hcpu0.toSameCpuState.readReg64 .lr)
      (by simpa [arm64_norm] using hrun0') fun sf hcpu_f _hcl_f hnsp_f hsym_f => ?_
    obtain ⟨hpres_f, hpool_f⟩ := allocCallPreserved_of_seg hcpu0 hcpu_f hnsp_f hsym_f
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq : A.pool lb lk s0 = A.pool lb lk sf := (A.pool_transport lb lk s0 sf hpool_f).symm
    have hpc_f : sf.pc = s0.readReg64 .lr := by
      rw [hcpu_f.toSameCpuState.pc_eq]; simp only [arm64_norm]; exact hcpu0.toSameCpuState.readReg64 .lr
    have hrun_f : sf.status = .Running :=
      hcpu_f.toSameCpuState.status_eq.trans (by simpa [arm64_norm] using hrun0')
    have hsp_f : sf.sp = s0.sp := by
      rw [hcpu_f.toSameCpuState.sp_eq]; simp [arm64_norm, hcpu0.toSameCpuState.sp_eq]
    have hcs_f : CalleeSavedPreserved s0 sf :=
      ((RvgHiCS.refl s0).of_seg hcpu0 hcpu_f (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])).to_cs
        (by rw [hcpu_f.toSameCpuState.readReg64 .x19]; simp only [arm64_norm]; exact hcpu0.toSameCpuState.readReg64 .x19)
        (by rw [hcpu_f.toSameCpuState.readReg64 .x20]; simp only [arm64_norm]; exact hcpu0.toSameCpuState.readReg64 .x20)
        (by rw [hcpu_f.toSameCpuState.readReg64 .x21]; simp only [arm64_norm]; exact hcpu0.toSameCpuState.readReg64 .x21)
        (by rw [hcpu_f.toSameCpuState.readReg64 .fp]; simp only [arm64_norm]; exact hcpu0.toSameCpuState.readReg64 .fp)
    refine SepWP.weaken_pre ?_ (SepWP.done hpc_f hrun_f ⟨fun hm_f => hm_f, hsp_f, hcs_f⟩)
    refine Entails.sepExists_right true ?_; simp only [↓reduceIte]
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right v2 ?_)
    rw [pure_sepConj_of_true (φ := AllocCallPreserved s0 sf ∧ NullAllowed newCap 1) ⟨hpres_f, hnull⟩,
        errnoCell_eq, hpool_eq, hcpu0.toSameCpuState.sp_eq, show 48 + finishStack = finishStack + 8 * 6 by omega,
        stackAt_split_cells s0.sp finishStack 6 (by omega)]
    dsimp only [cells, vecHeader]
    simp only [Nat.reduceMul, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, bv_lin_norm]
    refine Entails.sepExists_right (s0'.readReg64 (.gpr 29#5)) <|
      Entails.sepExists_right (s0'.readReg64 (.gpr 30#5)) <|
      Entails.sepExists_right (s0'.readReg64 (.gpr 21#5)) <|
      Entails.sepExists_right st3 <|
      Entails.sepExists_right (s0'.readReg64 (.gpr 20#5)) <|
      Entails.sepExists_right (s0'.readReg64 (.gpr 19#5)) (by sep_entail)

/-- Correctness of `<alloc::raw_vec::RawVecInner>::finish_grow` (block `22` of `rustStdIoMultiLib`)
    under `withCodeLoaded mpl` over any `(A : RustStdAlloc oom)`. -/
theorem rustFinishGrow_ok {oom : State → State → Prop} (A : RustStdAlloc oom)
    {mpl : MultiPlacement} (hpl : rustStdIoMultiLib.Placeable mpl)
    {P : Program} {finishStack : Nat}
    (hext : ∀ pc, P.externAt? pc = none)
    (hstk : Rust.hookStack ≤ finishStack ∧ 48 + finishStack ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustNoAllocShimIoSym)
      rustAllocShimSpec)
    (halloc : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustAllocIoSym)
      (rustStdAllocSpec A))
    (hrealloc : subroutine_ok P (rustStdIoMultiLib.resolve mpl rustReallocIoSym)
      (rustStdReallocSpec A)) :
    subroutine_ok P (rustStdIoMultiLib.resolve mpl finishGrowIoSym)
      (rustStdIoMultiLib.withCodeLoaded mpl (rustFinishGrowSpec A finishStack)) :=
  rustStdIoMultiLib.subroutine_ok_withCodeLoaded_of_where
    (rustFinishGrow_okWhere A hpl hext (keep := fun _ => true) (hk22 := rfl) hstk hshim halloc hrealloc)

end

end VerifiedLibraries.RustStd.Io
