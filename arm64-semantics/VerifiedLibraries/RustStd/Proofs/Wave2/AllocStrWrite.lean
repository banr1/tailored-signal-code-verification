/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Generated.AllocPlacedObj
public import VerifiedLibraries.RustStd.Spec.AllocStringClone
public import VerifiedLibraries.RustStd.Spec.AllocFormatInner
public import VerifiedLibraries.RustStd.Proofs.ExecSeg
public import VerifiedLibraries.RustStd.Proofs.FinishGrow
public import VerifiedLibraries.RustStd.Proofs.VecBridge
public import VerifiedLibraries.Musl.Spec.Top
public import ProofLib.GenPlacedFetches
public import ProofLib
public meta import ProofLib.ProgramReflection

/-!
# Specification and Proof for `<String as core::fmt::Write>::write_str`

Placement-generic, `{oom}`-polymorphic, panic-aware subroutine specification and proof for
`<alloc::string::String as core::fmt::Write>::write_str` (`allocBlocks[7]`), together with
`AllocPlacement`, `sepWP_seg_alloc_block_pure`, and `allocDoReserveSpec` (`allocBlocks[1]`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup

/-! ## Placement typeclass, symbols, and growth capacity helpers -/

/-- Placement typeclass for `VerifiedLibraries.RustStd.allocMultiLib`. -/
class AllocPlacement where
  mpl : MultiPlacement
  placeable : allocMultiLib.Placeable mpl

abbrev allocMpl [AllocPlacement] : MultiPlacement := AllocPlacement.mpl

/-- `P` installs no extern hooks inside code block `j` of `allocMultiLib`. -/
def AllocBlockNoExtern (mpl : MultiPlacement) (P : Program) (j : Nat) : Prop :=
  ∀ off : Nat, off < (allocMultiLib.blockLib j).text.code.length →
    P.externAt? (mpl.base j + BitVec.ofNat 64 off) = none

theorem AllocBlockNoExtern.of_no_extern {mpl : MultiPlacement} {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (j : Nat) :
    AllocBlockNoExtern mpl P j :=
  fun _ _ => hext _

abbrev allocStringWriteStrSym : String :=
  "<alloc::string::String as core::fmt::Write>::write_str [rust_alloc]"

abbrev allocDoReserveSym : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [rust_alloc]"

abbrev allocFinishGrowSym : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [rust_alloc]"

abbrev allocRustAllocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"

abbrev allocRustReallocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc"

abbrev allocRustNoAllocShimSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"

/-- Default stack budget below `sp` at entry to `alloc`'s `RawVecInner::do_reserve_and_handle`:
    `64` B (`do_reserve_and_handle`) + `32` B (`finish_grow`) + `4096` B (`Rust.hookStack`) = `4192` B. -/
abbrev defaultAllocReserveStack : Nat := 64 + 32 + Rust.hookStack

/-- Amortized capacity computed by `RawVecInner::do_reserve_and_handle` for `elem_size = 1`:
    `max (max (len + additional) (2 * cap)) 8`. -/
def allocVecGrowCap (cap len additional : Nat) : Nat :=
  max (max (len + additional) (2 * cap)) 8

/-- Updated budget units `lb'` after growing a `u8` buffer from `cap` to `growCap`
    (`alloc` when `cap = 0`, `realloc` when `0 < cap`, matching `AllocSeqFits` in `Spec/Alloc.lean`). -/
def allocVecGrowLb {oom : State → State → Prop} (A : RustStdAlloc oom)
    (lb cap growCap : Nat) : Nat :=
  if cap = 0 then lb + A.cost growCap 1
  else lb + A.cost growCap 1 - A.cost cap 1

/-- Updated live-block count `lk'` after growing a `u8` buffer from `cap` to `growCap`. -/
def allocVecGrowLk (lk cap : Nat) : Nat :=
  if cap = 0 then lk + 1 else lk

theorem allocResolve_eq_base {mpl : MultiPlacement} (hpl : allocMultiLib.Placeable mpl)
    (j : Nat) (sym : String) (hj : j < allocMultiLib.blocks.length)
    (hl : lookup sym allocMultiLib.blocks[j].symbols = some 0) :
    allocMultiLib.resolve mpl sym = mpl.base j := by
  have hblk := lookupBlockSym_of_lookup hj hpl.symbols_nodup hl
  simp [MultiPlacedLib.resolve, hblk]

/-! ## Block-scoped pure-segment lifter for `allocMultiLib` -/

private theorem strip_codeLoaded_alloc {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
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

private theorem strip_execOnlyIn_alloc (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) :=
  fun _ hpx => of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running_alloc {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem steps_rebase_lift_alloc_block {P R_j : Program}
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
    have hrb' : sb'.status = .Running := steps_start_running_alloc hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ => rw [hext_R] at he; cases he
    | extern_fault _ he _ => rw [hext_R] at he; cases he
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hL1' : R_j.CodeLoaded (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_codeLoaded_alloc hL1
      have hexec' : R_j.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_execOnlyIn_alloc R_j s1.mem
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

/-- Run a pure (non-syscall) segment of `allocMultiLib` block `j` up to `mid` from any `P : Program`
    with `AllocBlockNoExtern mpl P j`, refreshing `CodeLoaded` and supplying `SameCpuOracleState`,
    `NonSyscallPreserved`, and `sm.symtab = s.symtab`. -/
theorem sepWP_seg_alloc_block_pure {mpl : MultiPlacement} {P : Program}
    (j : Nat) (hj : j < allocMultiLib.blocks.length)
    (hext_blk : AllocBlockNoExtern mpl P j)
    (hchk : checkBlockNoSvc0 (allocMultiLib.blockLib j).text = true := by decide)
    {mid target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : allocMultiLib.CodeLoaded mpl s.mem)
    (hseg : ∀ s' : State, Io.SameCpuOracleState s' s →
      SepWP ((allocMultiLib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)) mid s' Pre
        (fun sm' Pm =>
          ∀ sm : State, Io.SameCpuOracleState sm sm' → allocMultiLib.CodeLoaded mpl sm.mem →
            ProofLib.NonSyscallPreserved s sm → sm.symtab = s.symtab →
            SepWP P target_pc sm Pm post oom)) :
    SepWP P target_pc s Pre post oom := by
  let R_j := (allocMultiLib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)
  let keep := ProofLib.progKeep R_j
  have hL_R : R_j.CodeLoaded s.mem := (hcl j hj).of_base_code rfl rfl
  have hext_R : ∀ pc, R_j.externAt? pc = none := by
    intro pc; exact MultiPlacedLib.externAt?_blockProgram_rebase_none _ _ _ _ _
  have hall : R_j.allInstrs (fun i => !i.isSvc0) = true :=
    blockProgram_rebase_allInstrs_not_isSvc0 allocMultiLib mpl j hchk
  have hext_R_blk : ∀ off : Nat, off < R_j.code.length →
      P.externAt? (R_j.base + BitVec.ofNat 64 off) = none := by
    intro off hoff
    have hlen : R_j.code.length ≤ (allocMultiLib.blockLib j).text.code.length := by
      change ((allocMultiLib.blockLib j).text.patched (allocMultiLib.blockPlacement mpl j)).length ≤ _
      rw [Obj.CodeBlock.length_patched]
      omega
    exact hext_blk off (Nat.lt_of_lt_of_le hoff hlen)
  refine SepWP.of_reaches_pc fun R hm => ?_
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hm
  have hcpu_in : Io.SameCpuOracleState (ProofLib.stripS keep s) s :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp [ProofLib.stripS]⟩
  obtain ⟨sm', hsteps', hout'⟩ :=
    SepWP.to_reaches_pc (hseg (ProofLib.stripS keep s) hcpu_in) hm_strip
      (strip_codeLoaded_alloc hL_R)
  rcases hout' with ⟨_, hrun_m', Pm, hmm', hcont⟩ | ⟨_, hoom⟩
  · obtain ⟨sm, hsm_eq, hsteps_P, hnsp⟩ :=
      steps_rebase_lift_alloc_block hext_R_blk hext_R hall hsteps' hrun_m' s rfl hL_R
    have hcl_m : allocMultiLib.CodeLoaded mpl sm.mem :=
      fun k hk => hsteps_P.codeLoaded (hcl k hk)
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := fun a => congrFun hnsp.2.1 a
    have hmm'_mem : ProofLib.stripExecOutside keep sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keep sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hcpu_out : Io.SameCpuOracleState sm sm' :=
      ⟨SameCpuState.of_stripS_left hsm_eq, by rw [hsm_eq]; simp [ProofLib.stripS]⟩
    have hwp_cont := hcont sm hcpu_out hcl_m hnsp hsteps_P.symtab_eq
    exact fun hL_P => by
      obtain ⟨sf, hsteps2, hout2⟩ := SepWP.to_reaches_pc hwp_cont hmm (hsteps_P.codeLoaded hL_P)
      exact ⟨sf, hsteps_P.trans hsteps2, hout2⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩
    exact False.elim hf

/-- Wrap `spec` with `allocMultiLib.CodeLoaded mpl` in both `pre` and `post` so callers in
    both `SepWP` and `SepWPp` (`SepWPp.call_wpp`) preserve `CodeLoaded` across calls. -/
def allocWithCodeLoaded {α : Type} (mpl : MultiPlacement) (spec : Spec α) : Spec α :=
  { allocMultiLib.withCodeLoaded mpl spec with
    post := fun x s0 sf => ⌜allocMultiLib.CodeLoaded mpl sf.mem⌝ ∗ spec.post x s0 sf }

/-- Drop the postcondition `CodeLoaded` witness from `allocWithCodeLoaded` to `withCodeLoaded`. -/
theorem subroutine_ok_of_allocWithCodeLoaded {α : Type}
    {mpl : MultiPlacement} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry (allocWithCodeLoaded mpl spec)) :
    subroutine_ok P entry (allocMultiLib.withCodeLoaded mpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine h.mono_outcome x R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [allocWithCodeLoaded] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr hrest


/-- Read-only source `memcpy` contract preserving `AllocCallPreserved` and `PoolPreserved`
    (so `IoCallFrame`, `fs`, `trace`, and `A.pool` all transport across `memcpy`). -/
def allocMemcpyROSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := stdMemcpyROSpec.pre
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ AllocCallPreserved s0 sf ∧ PoolPreserved s0 sf⌝ ∗
    ((dst ↦ₛ bs) ∗ (src ↦ᵣ bs))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-! ## Specifications: `allocDoReserveSpec` and `allocStringWriteStrSpec` -/

/-- `{oom}`-polymorphic, panic-aware contract for `liballoc`'s `RawVecInner::reserve::do_reserve_and_handle`
    (`allocBlocks[1]`, `120` B, `elem_align = 1, elem_size = 1` IPO-specialized), using `ioVecBuf A`
    from `VerifiedLibraries.RustStd.Spec.IoCommon`.
    Ghost: `(vecPtr, ptr, cap, bs, additional, lb, lk)`. -/
def allocDoReserveSpec {oom : State → State → Prop} (A : RustStdAlloc oom)
    (reserveStack : Nat := defaultAllocReserveStack) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) where
  pre := fun (vecPtr, ptr, cap, bs, additional, lb, lk) s0 =>
    let growCap := allocVecGrowCap cap.toNat bs.length additional
    ⌜s0.readReg64 .x0 = vecPtr ∧
      s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 additional ∧
      additional < 2 ^ 64 ∧
      cap.toNat - bs.length < additional ∧
      (bs.length + additional < 2 ^ 64 → growCap < 2 ^ 63 → A.CanAlloc lb lk growCap 1)⌝ ∗
    (stackAt s0.sp reserveStack ∗
      (vecPtr ↦₆₄ cap) ∗ ((vecPtr + 8#64) ↦₆₄ ptr) ∗
      ioVecBuf A cap ptr bs ∗
      A.pool lb lk s0 ∗
      StdErrnoCell s0.tpidrEl0)
  post := fun (vecPtr, _, cap, bs, additional, lb, lk) s0 sf =>
    let growCap := allocVecGrowCap cap.toNat bs.length additional
    ∃∗ newPtr : BitVec 64,
      ⌜AllocCallPreserved s0 sf ∧ growCap < 2 ^ 63⌝ ∗
      (stackAt s0.sp reserveStack ∗
        (vecPtr ↦₆₄ BitVec.ofNat 64 growCap) ∗ ((vecPtr + 8#64) ↦₆₄ newPtr) ∗
        ioVecBuf A (BitVec.ofNat 64 growCap) newPtr bs ∗
        A.pool (allocVecGrowLb A lb cap.toNat growCap) (allocVecGrowLk lk cap.toNat) sf ∗
        StdErrnoCell s0.tpidrEl0)
  onPanic := fun (_, _, cap, bs, additional, _, _) s0 sf =>
    ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
      (2 ^ 64 ≤ bs.length + additional ∨
        NullAllowed (allocVecGrowCap cap.toNat bs.length additional) 1)⌝ ∗ anyHeap
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ s0 sf => ⌜∃ sm, IoFrame s0 sm ∧ sm.fs = s0.fs ∧ oom sm sf⌝

/-- `{oom}`-polymorphic, panic-aware contract for `<alloc::string::String as core::fmt::Write>::write_str`
    (`allocBlocks[7]`, `124` B, `0x30`-byte stack frame), using `vecHeader` + `ioVecBuf A` from
    `VerifiedLibraries.RustStd.Spec.IoCommon`.
    Ghost: `(self, cap, ptr, bs, slicePtr, sbs, lb, lk)`. -/
def allocStringWriteStrSpec {oom : State → State → Prop} (A : RustStdAlloc oom)
    (reserveStack : Nat := defaultAllocReserveStack) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
      BitVec 64 × List (BitVec 8) × Nat × Nat) where
  pre := fun (self, cap, ptr, bs, slicePtr, sbs, lb, lk) s0 =>
    let growCap := allocVecGrowCap cap.toNat bs.length sbs.length
    ⌜s0.readReg64 .x0 = self ∧
      s0.readReg64 .x1 = slicePtr ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 sbs.length ∧
      sbs.length < 2 ^ 64 ∧
      (cap.toNat - bs.length < sbs.length →
        bs.length + sbs.length < 2 ^ 64 → growCap < 2 ^ 63 → A.CanAlloc lb lk growCap 1)⌝ ∗
    (stackAt s0.sp (48 + reserveStack) ∗
      vecHeader self cap ptr (BitVec.ofNat 64 bs.length) ∗
      ioVecBuf A cap ptr bs ∗
      (slicePtr ↦ᵣ sbs) ∗
      A.pool lb lk s0 ∗
      StdErrnoCell s0.tpidrEl0)
  post := fun (self, cap, ptr, bs, slicePtr, sbs, lb, lk) s0 sf =>
    let grew := decide (cap.toNat - bs.length < sbs.length)
    let growCap := allocVecGrowCap cap.toNat bs.length sbs.length
    let cap' : BitVec 64 := if grew then BitVec.ofNat 64 growCap else cap
    let lb' : Nat := if grew then allocVecGrowLb A lb cap.toNat growCap else lb
    let lk' : Nat := if grew then allocVecGrowLk lk cap.toNat else lk
    ⌜sf.readReg64 .x0 = 0#64 ∧
      AllocCallPreserved s0 sf ∧
      (grew = false → PoolPreserved s0 sf)⌝ ∗
    (stackAt s0.sp (48 + reserveStack) ∗
      (∃∗ ptr' : BitVec 64,
        ⌜grew = false → ptr' = ptr⌝ ∗
        vecHeader self cap' ptr' (BitVec.ofNat 64 (bs.length + sbs.length)) ∗
        ioVecBuf A cap' ptr' (bs ++ sbs)) ∗
      (slicePtr ↦ᵣ sbs) ∗
      A.pool lb' lk' sf ∗
      StdErrnoCell s0.tpidrEl0)
  onPanic := fun (_, cap, _, bs, _, sbs, _, _) s0 sf =>
    ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
      cap.toNat - bs.length < sbs.length ∧
      (2 ^ 64 ≤ bs.length + sbs.length ∨
        NullAllowed (allocVecGrowCap cap.toNat bs.length sbs.length) 1)⌝ ∗ anyHeap
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun (_, cap, _, bs, _, sbs, _, _) s0 sf =>
    ⌜cap.toNat - bs.length < sbs.length ∧
      ∃ sm, IoFrame s0 sm ∧ sm.fs = s0.fs ∧ oom sm sf⌝

/-! ## Block `7` (`write_str`) placement projections and fetch generation -/

def allocLib07 : PlacedLib := allocMultiLib.blockLib 7
def allocPl07 [AllocPlacement] : Placement := allocMultiLib.blockPlacement AllocPlacement.mpl 7
theorem allocPlaceable07 [AllocPlacement] : allocLib07.Placeable allocPl07 :=
  allocMultiLib.placeable_blockLib (by decide) AllocPlacement.placeable
def allocPC07 [AllocPlacement] : Program := allocLib07.program allocPl07

def allocProg07 : Program :=
  { code := allocLib07.text.code, symbols := allocLib07.text.symbols }
def allocTree07 : WordTree := word_tree_of% allocProg07
theorem alloc07_code_eq : allocLib07.text.code = allocTree07.toBytes := by rfl_kernel
theorem alloc07_tree_size : allocTree07.checkSize? = some 31 := by rfl_kernel
def allocSymChars07 : List (List Char × Nat) := sym_chars_of% allocProg07
theorem alloc07_symbols_eq : allocLib07.text.symbols = toStringSymbols allocSymChars07 := by rfl_kernel
theorem alloc07_symbols_fresh : allFreshCharSymbols allocSymChars07 = true := by rfl_kernel

section
set_option linter.literalFetch false
gen_placed_fetches allocPC07 allocLib07 allocTree07 alloc07_code_eq alloc07_tree_size
  via_placement allocPl07 allocPlaceable07 [0x0 → 0x78]
gen_placed_fnOffs allocPC07 allocLib07 allocSymChars07 alloc07_symbols_eq alloc07_symbols_fresh
end

theorem allocBlockNoSvc0_07 : checkBlockNoSvc0 (allocMultiLib.blockLib 7).text = true := by
  decide

theorem allocWriteStr_lookup :
    lookup allocStringWriteStrSym allocMultiLib.blocks[7].symbols = some 0 := by
  decide

theorem allocDoReserve_lookup :
    lookup allocDoReserveSym allocMultiLib.blocks[1].symbols = some 0 := by
  decide

theorem allocFinishGrow_lookup :
    lookup allocFinishGrowSym allocMultiLib.blocks[2].symbols = some 0 := by
  decide

/-! ## Proof of `<String as fmt::Write>::write_str` -/

section
arm64_proof_prelude

theorem allocVecGrowCap_ge (cap len additional : Nat) :
    len + additional ≤ allocVecGrowCap cap len additional := by
  unfold allocVecGrowCap; omega

theorem allocVecGrowCap_ge8 (cap len additional : Nat) :
    8 ≤ allocVecGrowCap cap len additional := by
  unfold allocVecGrowCap; omega

theorem allocSatisfies_ioVecBuf_bounds {oom : State → State → Prop} {A : RustStdAlloc oom}
    {m : Memory} {cap ptr : BitVec 64} {bs : List (BitVec 8)} {R : SepProp}
    (h : m ⊨ ioVecBuf A cap ptr bs ∗ R) :
    bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 := by
  unfold ioVecBuf at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.1

private abbrev allocWriteStrSavedSlots (s0 : State) : SepProp :=
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

private theorem allocWriteStr_stack_split (sp : BitVec 64) (reserveStack : Nat)
    (hstk : 48 + reserveStack ≤ 2 ^ 64) :
    stackAt sp (48 + reserveStack) =
      ∃∗ st0, ∃∗ st1, ∃∗ st2, ∃∗ st3, ∃∗ st4, ∃∗ st5,
        stackAt (sp - 48#64) reserveStack ∗
        (((sp - 48#64) ↦₆₄ st0) ∗ ((sp - 40#64) ↦₆₄ st1) ∗
          ((sp - 32#64) ↦₆₄ st2) ∗ ((sp - 24#64) ↦₆₄ st3) ∗
          ((sp - 16#64) ↦₆₄ st4) ∗ ((sp - 8#64) ↦₆₄ st5)) := by
  rw [show 48 + reserveStack = reserveStack + 8 * 6 by omega,
    stackAt_split_cells sp reserveStack 6 (by omega)]
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_right, bv_lin_norm]

private theorem allocWriteStr_stack_refold (sp : BitVec 64) (reserveStack : Nat)
    (hstk : 48 + reserveStack ≤ 2 ^ 64)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    stackAt (sp - 48#64) reserveStack ∗
      (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
        ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
        ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢
      stackAt sp (48 + reserveStack) := by
  rw [allocWriteStr_stack_split sp reserveStack hstk]
  exact Entails.sepExists_right w0 <| Entails.sepExists_right w1 <|
    Entails.sepExists_right w2 <| Entails.sepExists_right w3 <|
    Entails.sepExists_right w4 <| Entails.sepExists_right w5 <| Entails.refl _

private theorem allocWriteStr_memcpy_pc [AllocPlacement] :
    allocPl07.base + 60#64 + (allocPl07.ρ "memcpy" - allocPl07.base - 60#64) =
      allocMultiLib.resolve AllocPlacement.mpl "memcpy" := by
  change allocPl07.base + 60#64 +
    (allocMultiLib.resolve AllocPlacement.mpl "memcpy" - allocPl07.base - 60#64) =
    allocMultiLib.resolve AllocPlacement.mpl "memcpy"
  bv_lin

private theorem allocWriteStr_reserve_pc [AllocPlacement] :
    allocPl07.base + 108#64 + (allocPl07.ρ allocDoReserveSym - allocPl07.base - 108#64) =
      allocMultiLib.resolve AllocPlacement.mpl allocDoReserveSym := by
  change allocPl07.base + 108#64 +
    (allocMultiLib.resolve AllocPlacement.mpl allocDoReserveSym - allocPl07.base - 108#64) =
    allocMultiLib.resolve AllocPlacement.mpl allocDoReserveSym
  bv_lin

private theorem allocWriteStr_bhi_cond {cap : BitVec 64} {len slen : Nat}
    (hlen : len ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hslen : slen < 2 ^ 64) :
    ((cap - BitVec.ofNat 64 len).ult (BitVec.ofNat 64 slen)) = decide (cap.toNat - len < slen) := by
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    have hlen_bv : (BitVec.ofNat 64 len).toNat = len := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64)]
    rw [BitVec.toNat_sub_of_le]
    · omega
    · rw [BitVec.le_def, hlen_bv]; exact hlen
  have hslen_bv : (BitVec.ofNat 64 slen).toNat = slen := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hslen]
  simp only [BitVec.ult, hsub, hslen_bv]

private def WriteStrHighGprs (s0 s1 : State) : Prop :=
  s1.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  s1.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s1.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s1.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s1.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s1.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5)

private theorem WriteStrHighGprs.refl (s : State) : WriteStrHighGprs s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem WriteStrHighGprs.of_sameCpu {s' s : State} (h : SameCpuState s' s) :
    WriteStrHighGprs s s' :=
  ⟨h.readReg64 _, h.readReg64 _, h.readReg64 _, h.readReg64 _, h.readReg64 _, h.readReg64 _⟩

private theorem WriteStrHighGprs.trans {s0 s1 s2 : State}
    (h01 : WriteStrHighGprs s0 s1) (h12 : WriteStrHighGprs s1 s2) :
    WriteStrHighGprs s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.trans h01.2.2.2.2.2⟩

private theorem WriteStrHighGprs.of_calleeSaved {s0 s1 : State} (h : CalleeSavedPreserved s0 s1) :
    WriteStrHighGprs s0 s1 :=
  ⟨h.readReg64_x23, h.readReg64_x24, h.readReg64_x25,
   h.readReg64_x26, h.readReg64_x27, h.readReg64_x28⟩

private theorem allocWriteStr_from_memcpy [AllocPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program}
    (hext7 : AllocBlockNoExtern allocMpl P 7)
    (hmemcpy : subroutine_ok P (allocMultiLib.resolve allocMpl "memcpy") allocMemcpyROSpec)
    {s0 sm_mc : State} {self cap' ptr' slicePtr : BitVec 64}
    {bs sbs : List (BitVec 8)} {lb' lk' reserveStack : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hstk : 48 + reserveStack ≤ 2 ^ 64)
    (hcl : allocMultiLib.CodeLoaded allocMpl sm_mc.mem)
    (hpc : sm_mc.pc = allocMultiLib.resolve allocMpl "memcpy")
    (hrun : sm_mc.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : sm_mc.sp = s0.sp - 48#64)
    (hlr : sm_mc.readReg64 .lr =
      allocPl07.base + (reloc_call_off% allocLib07.text.relocs "memcpy" + 4#64))
    (hx0 : sm_mc.readReg64 .x0 = ptr' + BitVec.ofNat 64 bs.length)
    (hx1 : sm_mc.readReg64 .x1 = slicePtr)
    (hx2 : sm_mc.readReg64 .x2 = BitVec.ofNat 64 sbs.length)
    (hx19 : sm_mc.readReg64 (.gpr 19#5) = self)
    (hx20 : sm_mc.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length)
    (hx21 : sm_mc.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length)
    (hgprs : WriteStrHighGprs s0 sm_mc)
    (hvregs : calleeSavedVRegs sm_mc = calleeSavedVRegs s0)
    (hsbs_pos : 0 < sbs.length)
    (hfit : sbs.length ≤ cap'.toNat - bs.length)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      AllocCallPreserved sm_mc sf → PoolPreserved sm_mc sf →
      sf.readReg64 .x0 = 0#64 →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp (48 + reserveStack) ∗
          vecHeader self cap' ptr' (BitVec.ofNat 64 (bs.length + sbs.length)) ∗
          ioVecBuf A cap' ptr' (bs ++ sbs) ∗
          (slicePtr ↦ᵣ sbs) ∗ A.pool lb' lk' sf ∗ StdErrnoCell s0.tpidrEl0) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sm_mc
      (ioVecBuf A cap' ptr' bs ∗
        (stackAt (s0.sp - 48#64) reserveStack ∗ allocWriteStrSavedSlots s0 ∗
          vecHeader self cap' ptr' (BitVec.ofNat 64 bs.length) ∗
          (slicePtr ↦ᵣ sbs) ∗ A.pool lb' lk' sm_mc ∗ StdErrnoCell s0.tpidrEl0))
      post oomProp := by
  wp_conv_pre => simp only [ioVecBuf, sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hbs_le, hcap'_lt, hptr'_ne⟩
  have hcap'_pos : 0 < cap'.toNat := by omega
  have hcap'_ne0 : cap' ≠ 0#64 := by
    intro h0; subst h0; simp at hcap'_pos
  wp_conv_pre => simp only [hcap'_ne0, ↓reduceIte, sepConj_assoc]
  have hsp_mc : sm_mc.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_eq]; exact s0.spAligned_sub 48#64 hsp0
  wp_conv_pre =>
    rw [memRegion_split_le (ptr' + BitVec.ofNat 64 bs.length) sbs.length (cap'.toNat - bs.length)
      hfit (by omega)]
  apply seqCodeLoaded hcl (mid := allocPl07.base + (reloc_call_off% allocLib07.text.relocs "memcpy" + 4#64))
  apply (SepWP.call_subroutine_frame hmemcpy
    (x := (ptr' + BitVec.ofNat 64 bs.length, slicePtr, sbs))
    hpc hrun hsp_mc hlr
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [allocMemcpyROSpec, stdMemcpyROSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, by omega⟩, Satisfies.mono (by sep_frame) hm'⟩
  · intro sf_mc hpc_sfmc hrun_sfmc hsp_sfmc hcs_sfmc
    refine SepWP.done hpc_sfmc hrun_sfmc fun hcl_sfmc => ?_
    dsimp only [allocMemcpyROSpec]
    wp_conv_pre => simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨_, hacp_mc, hpool_mc⟩
    have hpool_eq_mc : A.pool lb' lk' sm_mc = A.pool lb' lk' sf_mc :=
      (A.pool_transport lb' lk' sm_mc sf_mc hpool_mc).symm
    have hsp_sfmc_eq : sf_mc.sp = s0.sp - 48#64 := hsp_sfmc.trans hsp_eq
    have hx19_sfmc : sf_mc.readReg64 (.gpr 19#5) = self :=
      hcs_sfmc.readReg64_x19.trans hx19
    have hx20_sfmc : sf_mc.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length :=
      hcs_sfmc.readReg64_x20.trans hx20
    have hx21_sfmc : sf_mc.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length :=
      hcs_sfmc.readReg64_x21.trans hx21
    have hgprs_sfmc : WriteStrHighGprs s0 sf_mc :=
      hgprs.trans (WriteStrHighGprs.of_calleeSaved hcs_sfmc)
    have hvregs_sfmc : calleeSavedVRegs sf_mc = calleeSavedVRegs s0 :=
      hcs_sfmc.vregs.trans hvregs
    apply sepWP_seg_alloc_block_pure 7 (by decide) hext7 allocBlockNoSvc0_07 hcl_sfmc
      (mid := s0.readReg64 .lr)
    intro se' hcpu_e0
    have hcpu_e := hcpu_e0.1
    change SepWP (allocPC07.rebase allocPl07.base (fun _ => none)) _ _ _ _
    have hpc_e' : se'.pc = allocPl07.base + 64#64 :=
      hcpu_e.pc_eq.trans hpc_sfmc
    have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun_sfmc
    have hsp_e_in : se'.sp = s0.sp - 48#64 := hcpu_e.sp_eq.trans hsp_sfmc_eq
    have hsp_e' : se'.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_e_in]; exact s0.spAligned_sub 48#64 hsp0
    have hx19_e' : se'.readReg64 (.gpr 19#5) = self := (hcpu_e.readReg64 _).trans hx19_sfmc
    have hx20_e' : se'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length :=
      (hcpu_e.readReg64 _).trans hx20_sfmc
    have hx21_e' : se'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length :=
      (hcpu_e.readReg64 _).trans hx21_sfmc
    wp_conv_pre =>
      simp only [allocWriteStrSavedSlots, vecHeader, hpool_eq_mc, ← hsp_e_in,
        show s0.sp - 40#64 = se'.sp + 8#64 by rw [hsp_e_in]; bv_lin,
        show s0.sp - 32#64 = se'.sp + 16#64 by rw [hsp_e_in]; bv_lin,
        show s0.sp - 24#64 = se'.sp + 24#64 by rw [hsp_e_in]; bv_lin,
        show s0.sp - 16#64 = se'.sp + 32#64 by rw [hsp_e_in]; bv_lin,
        show s0.sp - 8#64 = se'.sp + 40#64 by rw [hsp_e_in]; bv_lin]
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
      fun sf hcpu_f0 _hcl_f hnsp_f hsym_f => ?_
    have hcpu_f := hcpu_f0.1
    have ⟨hacp_ef, hpool_ef⟩ :=
      Io.allocCallPreserved_of_seg hcpu_e0 hcpu_f0 hnsp_f hsym_f
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_ef : A.pool lb' lk' sf_mc = A.pool lb' lk' sf :=
      (A.pool_transport lb' lk' sf_mc sf hpool_ef).symm
    have hpc_f : sf.pc = s0.readReg64 .lr := by
      rw [hcpu_f.pc_eq]; simp [arm64_norm]
    have hrun_f : sf.status = .Running :=
      hcpu_f.status_eq.trans (by simpa [arm64_norm] using hrun_e')
    have hsp_f : sf.sp = s0.sp := by
      rw [hcpu_f.sp_eq]; simp [arm64_norm]
    have hx0_f : sf.readReg64 .x0 = 0#64 := by
      rw [hcpu_f.readReg64 .x0]; simp [arm64_norm]
    have hcs_f : CalleeSavedPreserved s0 sf := by
      rw [CalleeSavedPreserved.iff_regs]
      have hg := hgprs_sfmc
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcpu_f.readReg64]; simp [arm64_norm]
      · rw [hcpu_f.readReg64]; simp [arm64_norm]
      · rw [hcpu_f.readReg64]; simp [arm64_norm]
      · rw [hcpu_f.readReg64]; simp [arm64_norm]
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hg.1
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hg.2.1
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hg.2.2.1
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hg.2.2.2.1
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hg.2.2.2.2.1
      · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hg.2.2.2.2.2
      · rw [hcpu_f.readReg64]; simp [arm64_norm]
      · exact hcpu_f.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
            (hcpu_e.calleeSavedVRegs.trans hvregs_sfmc))
    refine SepWP.done hpc_f hrun_f
      (hcont sf hpc_f hrun_f hsp_f hcs_f
        (Io.allocCallPreserved_trans hacp_mc hacp_ef)
        (Io.poolPreserved_trans hpool_mc hpool_ef)
        hx0_f ?_)
    have hstk_back := allocWriteStr_stack_refold s0.sp reserveStack hstk
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
      (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
      (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
    dsimp only [ioVecBuf, vecHeader]
    simp only [hcap'_ne0, ↓reduceIte, hsp_e_in]
    rw [pure_sepConj_of_true ⟨by simp [List.length_append]; omega, hcap'_lt, hptr'_ne⟩,
      pointsToBytes_append (a := ptr'),
      show ptr' + BitVec.ofNat 64 (bs ++ sbs).length =
        ptr' + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 sbs.length by
        rw [List.length_append, BitVec.ofNat_add, BitVec.add_assoc],
      show cap'.toNat - (bs ++ sbs).length = cap'.toNat - bs.length - sbs.length by
        simp [List.length_append]; omega,
      show BitVec.ofNat 64 bs.length + BitVec.ofNat 64 sbs.length =
        BitVec.ofNat 64 (bs.length + sbs.length) by
        rw [BitVec.ofNat_add],
      hpool_eq_ef]
    simp only [bv_lin_norm]
    refine Entails.trans ?_ (sepConj_mono_left hstk_back)
    sep_entail

set_option maxHeartbeats 800000 in
/-- Placement-generic, `{oom}`-polymorphic, panic-aware proof of
    `<alloc::string::String as core::fmt::Write>::write_str` (`allocBlocks[7]`, `124` B)
    given `hreserve` (`allocDoReserveSpec A reserveStack`) and `hmemcpy` (`allocMemcpyROSpec`). -/
theorem allocStringWriteStr_ok_of_reserve {oom : State → State → Prop} (A : RustStdAlloc oom)
    {mpl : MultiPlacement} (hpl : allocMultiLib.Placeable mpl)
    {P : Program} {reserveStack : Nat}
    (hext7 : AllocBlockNoExtern mpl P 7)
    (hstk : 48 + reserveStack ≤ 2 ^ 64 := by decide)
    (hmemcpy : subroutine_ok P (allocMultiLib.resolve mpl "memcpy") allocMemcpyROSpec)
    (hreserve : subroutine_ok P (allocMultiLib.resolve mpl allocDoReserveSym)
      (allocWithCodeLoaded mpl (allocDoReserveSpec A reserveStack))) :
    subroutine_ok P (allocMultiLib.resolve mpl allocStringWriteStrSym)
      (allocMultiLib.withCodeLoaded mpl (allocStringWriteStrSpec A reserveStack)) := by
  letI : AllocPlacement := ⟨mpl, hpl⟩
  rw [allocResolve_eq_base hpl 7 allocStringWriteStrSym (by decide) allocWriteStr_lookup]
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨self, cap, ptr, bs, slicePtr, sbs, lb, lk⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, allocStringWriteStrSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜allocMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hsbs_lt, hgrow_pre⟩, hmem⟩
  have ⟨hbs_le, hcap_lt, _hptr_ne⟩ : bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 :=
    allocSatisfies_ioVecBuf_bounds (m := s0.mem)
      (R := stackAt s0.sp (48 + reserveStack) ∗ vecHeader self cap ptr (BitVec.ofNat 64 bs.length) ∗
        (slicePtr ↦ᵣ sbs) ∗ A.pool lb lk s0 ∗ StdErrnoCell s0.tpidrEl0 ∗ R)
      (Satisfies.mono (by sep_entail) hmem)
  refine ⟨_, hmem, ?_⟩
  conv =>
    arg 4
    rw [allocWriteStr_stack_split s0.sp reserveStack hstk]
    simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun st0 => SepWPp.exists_elim fun st1 =>
    SepWPp.exists_elim fun st2 => SepWPp.exists_elim fun st3 =>
    SepWPp.exists_elim fun st4 => SepWPp.exists_elim fun st5 => ?_
  by_cases hgt : cap.toNat - bs.length < sbs.length
  ·
    have hgrew : decide (cap.toNat - bs.length < sbs.length) = true := decide_eq_true hgt
    have hsbs_pos : 0 < sbs.length := by omega
    have hcan := hgrow_pre hgt
    have hbhi : ((cap - BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 sbs.length)) = true := by
      rw [allocWriteStr_bhi_cond hbs_le hcap_lt hsbs_lt, hgrew]
    apply SepWPp.seq_frozen (mid := allocMultiLib.resolve mpl allocDoReserveSym)
      (fun _ _ (h : allocMultiLib.CodeLoaded mpl _) hkf => h.of_keepsFrozen hkf) hcl0
    apply sepWP_seg_alloc_block_pure 7 (by decide) hext7 allocBlockNoSvc0_07 hcl0
      (mid := allocMultiLib.resolve mpl allocDoReserveSym)
    intro s1' hcpu1_0
    have hcpu1 := hcpu1_0.1
    change SepWP (allocPC07.rebase allocPl07.base (fun _ => none)) _ _ _ _
    have hpc1' : s1'.pc = allocPl07.base := hcpu1.pc_eq.trans hpc
    have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
    have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
    have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
    have hx0_1' : s1'.readReg64 (.gpr 0#5) = self := (hcpu1.readReg64 .x0).trans hx0
    have hx1_1' : s1'.readReg64 (.gpr 1#5) = slicePtr := (hcpu1.readReg64 .x1).trans hx1
    have hx2_1' : s1'.readReg64 (.gpr 2#5) = BitVec.ofNat 64 sbs.length := (hcpu1.readReg64 .x2).trans hx2
    have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) := hcpu1.readReg64 _
    have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
    have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
    have hx21_1' : s1'.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) := hcpu1.readReg64 _
    have hx22_1' : s1'.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) := hcpu1.readReg64 _
    have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
    wp_conv_pre => simp only [vecHeader, ← hsp1_in]
    wp_sym_steps
    refine SepWP.done allocWriteStr_reserve_pc (by simpa [arm64_norm] using hrun1')
      fun sm_res hcpu_mres0 hcl_mres hnsp_mres hsym_mres => ?_
    have hcpu_mres := hcpu_mres0.1
    have ⟨hacp_0res, hpool_0res⟩ :=
      Io.allocCallPreserved_of_seg hcpu1_0 hcpu_mres0 hnsp_mres hsym_mres
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_0res : A.pool lb lk s0 = A.pool lb lk sm_res :=
      (A.pool_transport lb lk s0 sm_res hpool_0res).symm
    have hpc_mres : sm_res.pc = allocMultiLib.resolve mpl allocDoReserveSym :=
      hcpu_mres.pc_eq.trans allocWriteStr_reserve_pc
    have hrun_mres : sm_res.status = .Running := hcpu_mres.status_eq.trans hrun1'
    have hsp_mres_eq : sm_res.sp = s0.sp - 48#64 :=
      hcpu_mres.sp_eq.trans (by simp [arm64_norm])
    have hsp_mres : sm_res.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_mres_eq]; exact s0.spAligned_sub 48#64 hsp0
    have hlr_mres : sm_res.readReg64 .lr =
        allocPl07.base + (reloc_call_off% allocLib07.text.relocs
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [rust_alloc]" + 4#64) := by
      rw [hcpu_mres.readReg64 .lr]; simp [arm64_norm]
    have hx0_mres : sm_res.readReg64 .x0 = self := by
      rw [hcpu_mres.readReg64 .x0]; simp [arm64_norm]
    have hx1_mres : sm_res.readReg64 .x1 = BitVec.ofNat 64 bs.length := by
      rw [hcpu_mres.readReg64 .x1]; simp [arm64_norm]
    have hx2_mres : sm_res.readReg64 .x2 = BitVec.ofNat 64 sbs.length := by
      rw [hcpu_mres.readReg64 .x2]; simp [arm64_norm]
    have hx19_mres : sm_res.readReg64 (.gpr 19#5) = self := by
      rw [hcpu_mres.readReg64]; simp [arm64_norm]
    have hx20_mres : sm_res.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length := by
      rw [hcpu_mres.readReg64]; simp [arm64_norm]
    have hx22_mres : sm_res.readReg64 (.gpr 22#5) = slicePtr := by
      rw [hcpu_mres.readReg64]; simp [arm64_norm]
    have hgprs_mres : WriteStrHighGprs s0 sm_res := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hcpu_mres.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
    have hvregs_mres : calleeSavedVRegs sm_res = calleeSavedVRegs s0 :=
      hcpu_mres.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
    wp_conv_pre => simp only [hsp1_in, hpool_eq_0res]
    refine SepWP.done hpc_mres hrun_mres fun _hcl_mres' => ?_
    apply (SepWPp.call_wpp hreserve
      (x := (self, ptr, cap, bs, sbs.length, lb, lk))
      hpc_mres hrun_mres hsp_mres hlr_mres
      (hoom := fun sf_oom R' _ hm_oom => by
        have hm' := Satisfies.drop_mid hm_oom
        dsimp only [allocWithCodeLoaded, MultiPlacedLib.withCodeLoaded, allocDoReserveSpec] at hm'
        rw [satisfies_pure_sepConj] at hm' ⊢
        rcases hm'.1 with ⟨sm, hio_sm, hfs_sm, hoom_sm⟩
        exact ⟨⟨hgt, sm,
          ⟨hio_sm.1.trans hacp_0res.2.1, hio_sm.2.trans hacp_0res.2.2.1⟩,
          hfs_sm.trans hacp_0res.1, hoom_sm⟩, hm'.2⟩))
    ·
      intro R' hm'
      dsimp only [allocWithCodeLoaded, MultiPlacedLib.withCodeLoaded, allocDoReserveSpec]
      rw [sepConj_comm _ ⌜allocMultiLib.CodeLoaded mpl sm_res.mem⌝, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨hcl_mres, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      rw [hsp_mres_eq, hacp_0res.2.2.2.1]
      exact ⟨⟨hx0_mres, hx1_mres, hx2_mres, hsbs_lt, hgt, hcan⟩,
        Satisfies.mono (by sep_frame) hm'⟩
    ·
      intro _ _ _ _ h
      exact not_satisfies_false_sepConj h
    ·
      intro sf_pan _ _ hm_pan
      dsimp only [allocWithCodeLoaded, MultiPlacedLib.withCodeLoaded, allocDoReserveSpec] at hm_pan
      exact allowPanic_frame
        (fun ⟨hfs, htr, hp⟩ => ⟨hfs.trans hacp_0res.1, htr.trans hacp_0res.2.1, hgt, hp⟩) hm_pan
    ·
      intro sf_res hpc_sfres hrun_sfres hsp_sfres hcs_sfres
      apply SepWPp.of_sepWP_ret
      dsimp only [allocWithCodeLoaded, MultiPlacedLib.withCodeLoaded, allocDoReserveSpec]
      wp_conv_pre => simp only [sepConj_assoc]
      apply SepWP.pure_elim; intro hcl_sfres
      wp_conv_pre => rw [sepExists_sepConj_left]
      refine SepWP.exists_elim fun newPtr => ?_
      wp_conv_pre => simp only [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hacp_res, hgrow_lt63⟩
      have hsp_sfres_eq : sf_res.sp = s0.sp - 48#64 := hsp_sfres.trans hsp_mres_eq
      have hx19_sfres : sf_res.readReg64 (.gpr 19#5) = self :=
        hcs_sfres.readReg64_x19.trans hx19_mres
      have hx20_sfres : sf_res.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length :=
        hcs_sfres.readReg64_x20.trans hx20_mres
      have hx22_sfres : sf_res.readReg64 (.gpr 22#5) = slicePtr :=
        hcs_sfres.readReg64_x22.trans hx22_mres
      have hgprs_sfres : WriteStrHighGprs s0 sf_res :=
        hgprs_mres.trans (WriteStrHighGprs.of_calleeSaved hcs_sfres)
      have hvregs_sfres : calleeSavedVRegs sf_res = calleeSavedVRegs s0 :=
        hcs_sfres.vregs.trans hvregs_mres
      let growCap := allocVecGrowCap cap.toNat bs.length sbs.length
      let lb' := allocVecGrowLb A lb cap.toNat growCap
      let lk' := allocVecGrowLk lk cap.toNat
      have hgrow_toNat : (BitVec.ofNat 64 growCap).toNat = growCap := by
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : growCap < 2 ^ 64)]
      have hfit_grow : sbs.length ≤ (BitVec.ofNat 64 growCap).toNat - bs.length := by
        have := allocVecGrowCap_ge cap.toNat bs.length sbs.length
        rw [hgrow_toNat]; omega
      apply sepWP_seg_alloc_block_pure 7 (by decide) hext7 allocBlockNoSvc0_07 hcl_sfres
        (mid := allocMultiLib.resolve mpl "memcpy")
      intro sj' hcpu_j0
      have hcpu_j := hcpu_j0.1
      change SepWP (allocPC07.rebase allocPl07.base (fun _ => none)) _ _ _ _
      have hpc_j' : sj'.pc = allocPl07.base + 112#64 := hcpu_j.pc_eq.trans hpc_sfres
      have hrun_j' : sj'.status = .Running := hcpu_j.status_eq.trans hrun_sfres
      have hsp_j_in : sj'.sp = s0.sp - 48#64 := hcpu_j.sp_eq.trans hsp_sfres_eq
      have hsp_j' : sj'.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_j_in]; exact s0.spAligned_sub 48#64 hsp0
      have hx19_j' : sj'.readReg64 (.gpr 19#5) = self := (hcpu_j.readReg64 _).trans hx19_sfres
      have hx20_j' : sj'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length :=
        (hcpu_j.readReg64 _).trans hx20_sfres
      have hx22_j' : sj'.readReg64 (.gpr 22#5) = slicePtr :=
        (hcpu_j.readReg64 _).trans hx22_sfres
      wp_sym_steps
      refine SepWP.done allocWriteStr_memcpy_pc (by simpa [arm64_norm] using hrun_j')
        fun sm_mc hcpu_mc0 hcl_mc hnsp_mc hsym_mc => ?_
      have hcpu_mc := hcpu_mc0.1
      have ⟨hacp_jmc, hpool_jmc⟩ :=
        Io.allocCallPreserved_of_seg hcpu_j0 hcpu_mc0 hnsp_mc hsym_mc
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_jmc : A.pool lb' lk' sf_res = A.pool lb' lk' sm_mc :=
        (A.pool_transport lb' lk' sf_res sm_mc hpool_jmc).symm
      have hpc_mc : sm_mc.pc = allocMultiLib.resolve mpl "memcpy" :=
        hcpu_mc.pc_eq.trans allocWriteStr_memcpy_pc
      have hrun_mc : sm_mc.status = .Running := hcpu_mc.status_eq.trans hrun_j'
      have hsp_mc_eq : sm_mc.sp = s0.sp - 48#64 :=
        (hcpu_mc.sp_eq.trans (by simp [arm64_norm])).trans hsp_j_in
      have hlr_mc : sm_mc.readReg64 .lr =
          allocPl07.base + (reloc_call_off% allocLib07.text.relocs "memcpy" + 4#64) := by
        rw [hcpu_mc.readReg64 .lr]; simp [arm64_norm]
      have hx0_mc : sm_mc.readReg64 .x0 = newPtr + BitVec.ofNat 64 bs.length := by
        rw [hcpu_mc.readReg64 .x0]; simp [arm64_norm]
      have hx1_mc : sm_mc.readReg64 .x1 = slicePtr := by
        rw [hcpu_mc.readReg64 .x1]; simp [arm64_norm]
      have hx2_mc : sm_mc.readReg64 .x2 = BitVec.ofNat 64 sbs.length := by
        rw [hcpu_mc.readReg64 .x2]; simp [arm64_norm]
      have hx19_mc : sm_mc.readReg64 (.gpr 19#5) = self := by
        rw [hcpu_mc.readReg64]; simpa [arm64_norm] using hx19_j'
      have hx20_mc : sm_mc.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length := by
        rw [hcpu_mc.readReg64]; simpa [arm64_norm] using hx20_j'
      have hx21_mc : sm_mc.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length := by
        rw [hcpu_mc.readReg64]; simp [arm64_norm]
      have hgprs_mc : WriteStrHighGprs s0 sm_mc := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hcpu_mc.readReg64]; simpa [arm64_norm] using (hcpu_j.readReg64 _).trans hgprs_sfres.1
        · rw [hcpu_mc.readReg64]; simpa [arm64_norm] using (hcpu_j.readReg64 _).trans hgprs_sfres.2.1
        · rw [hcpu_mc.readReg64]; simpa [arm64_norm] using (hcpu_j.readReg64 _).trans hgprs_sfres.2.2.1
        · rw [hcpu_mc.readReg64]; simpa [arm64_norm] using (hcpu_j.readReg64 _).trans hgprs_sfres.2.2.2.1
        · rw [hcpu_mc.readReg64]; simpa [arm64_norm] using (hcpu_j.readReg64 _).trans hgprs_sfres.2.2.2.2.1
        · rw [hcpu_mc.readReg64]; simpa [arm64_norm] using (hcpu_j.readReg64 _).trans hgprs_sfres.2.2.2.2.2
      have hvregs_mc : calleeSavedVRegs sm_mc = calleeSavedVRegs s0 :=
        hcpu_mc.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs sj').trans
            (hcpu_j.calleeSavedVRegs.trans hvregs_sfres))
      have hacp_0mc : AllocCallPreserved s0 sm_mc :=
        Io.allocCallPreserved_trans hacp_0res (Io.allocCallPreserved_trans hacp_res hacp_jmc)
      refine SepWP.weaken_pre (by
        rw [hsp_mres_eq, hpool_eq_jmc, hacp_0res.2.2.2.1]
        dsimp only [allocWriteStrSavedSlots, vecHeader]
        sep_entail) <|
        allocWriteStr_from_memcpy A hext7 hmemcpy hstk hcl_mc hpc_mc hrun_mc hsp0 hsp_mc_eq
          hlr_mc hx0_mc hx1_mc hx2_mc hx19_mc hx20_mc hx21_mc hgprs_mc hvregs_mc hsbs_pos hfit_grow
          fun sf _ _ hsp_f hcs_f hacp_mcf _hpool_mcf hx0_f {_Pre_f} hent =>
            ⟨fun hm_out => Satisfies.mono (sepConj_mono_left (Entails.trans hent (by
              simp only [hgrew, ↓reduceIte]
              rw [pure_sepConj_of_true ⟨hx0_f,
                Io.allocCallPreserved_trans hacp_0mc hacp_mcf,
                fun h => Bool.noConfusion h⟩]
              refine Entails.trans ?_
                (sepConj_mono_right (sepConj_mono_left
                  (Entails.sepExists_right newPtr (Entails.refl _))))
              rw [pure_sepConj_of_true (fun h => Bool.noConfusion h)]
              sep_entail))) hm_out, hsp_f, hcs_f⟩
  ·
    apply SepWPp.of_sepWP_ret
    have hle : sbs.length ≤ cap.toNat - bs.length := Nat.le_of_not_lt hgt
    have hgrew : decide (cap.toNat - bs.length < sbs.length) = false := decide_eq_false hgt
    have hbhi : ((cap - BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 sbs.length)) = false := by
      rw [allocWriteStr_bhi_cond hbs_le hcap_lt hsbs_lt, hgrew]
    by_cases hsbs0 : sbs.length = 0
    ·
      have hsbs_nil : sbs = [] := List.eq_nil_of_length_eq_zero hsbs0
      apply sepWP_seg_alloc_block_pure 7 (by decide) hext7 allocBlockNoSvc0_07 hcl0
        (mid := s0.readReg64 .lr)
      intro s1' hcpu1_0
      have hcpu1 := hcpu1_0.1
      change SepWP (allocPC07.rebase allocPl07.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = allocPl07.base := hcpu1.pc_eq.trans hpc
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 (.gpr 0#5) = self := (hcpu1.readReg64 .x0).trans hx0
      have hx2_1' : s1'.readReg64 (.gpr 2#5) = 0#64 :=
        (hcpu1.readReg64 .x2).trans (hx2.trans (by simp [hsbs0]))
      have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 .lr := hcpu1.readReg64 .lr
      have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
      have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
      have hx21_1' : s1'.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) := hcpu1.readReg64 _
      have hx22_1' : s1'.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) := hcpu1.readReg64 _
      have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
      have hbhi0 : ((cap - BitVec.ofNat 64 bs.length).ult 0#64) = false := by simp [BitVec.ult]
      wp_conv_pre => simp only [vecHeader, ← hsp1_in]
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1')
        fun sf hcpu_f0 _hcl_f hnsp_f hsym_f => ?_
      have hcpu_f := hcpu_f0.1
      have ⟨hacp_0f, hpool_0f⟩ :=
        Io.allocCallPreserved_of_seg hcpu1_0 hcpu_f0 hnsp_f hsym_f
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_0f : A.pool lb lk s0 = A.pool lb lk sf :=
        (A.pool_transport lb lk s0 sf hpool_0f).symm
      have hpc_f : sf.pc = s0.readReg64 .lr := by
        rw [hcpu_f.pc_eq]; simp [arm64_norm]
      have hrun_f : sf.status = .Running :=
        hcpu_f.status_eq.trans (by simpa [arm64_norm] using hrun1')
      have hsp_f : sf.sp = s0.sp := by
        rw [hcpu_f.sp_eq]; simp [arm64_norm]
      have hx0_f : sf.readReg64 .x0 = 0#64 := by
        rw [hcpu_f.readReg64 .x0]; simp [arm64_norm]
      have hcs_f : CalleeSavedPreserved s0 sf := by
        rw [CalleeSavedPreserved.iff_regs]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hcpu_f.readReg64]; simp [arm64_norm]
        · rw [hcpu_f.readReg64]; simp [arm64_norm]
        · rw [hcpu_f.readReg64]; simp [arm64_norm]
        · rw [hcpu_f.readReg64]; simp [arm64_norm]
        · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
        · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
        · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
        · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
        · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
        · rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
        · rw [hcpu_f.readReg64]; simp [arm64_norm]
        · exact hcpu_f.calleeSavedVRegs.trans
            ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
      refine SepWP.done hpc_f hrun_f
        ⟨fun hm_f => Satisfies.mono (sepConj_mono_left ?_) hm_f, hsp_f, hcs_f⟩
      have hstk_back := allocWriteStr_stack_refold s0.sp reserveStack hstk
        (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
        (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
        (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
      simp only [hgrew, Bool.false_eq_true, ↓reduceIte]
      rw [hsbs0, Nat.add_zero, hsbs_nil, List.append_nil]
      simp only [hsp1_in, hpool_eq_0f, vecHeader, bv_lin_norm]
      rw [pure_sepConj_of_true ⟨hx0_f, hacp_0f, fun _ => hpool_0f⟩]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right ptr (Entails.refl _))))
      rw [pure_sepConj_of_true (fun _ => rfl)]
      refine Entails.trans ?_ (sepConj_mono_left hstk_back)
      sep_entail
    ·
      have hsbs_pos : 0 < sbs.length := Nat.pos_of_ne_zero hsbs0
      have hsbs_ne0 : BitVec.ofNat 64 sbs.length ≠ 0#64 := by bv_omega
      have hsbs_beq0 : (BitVec.ofNat 64 sbs.length == 0#64) = false := beq_false_of_ne hsbs_ne0
      apply sepWP_seg_alloc_block_pure 7 (by decide) hext7 allocBlockNoSvc0_07 hcl0
        (mid := allocMultiLib.resolve mpl "memcpy")
      intro s1' hcpu1_0
      have hcpu1 := hcpu1_0.1
      change SepWP (allocPC07.rebase allocPl07.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = allocPl07.base := hcpu1.pc_eq.trans hpc
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 (.gpr 0#5) = self := (hcpu1.readReg64 .x0).trans hx0
      have hx1_1' : s1'.readReg64 (.gpr 1#5) = slicePtr := (hcpu1.readReg64 .x1).trans hx1
      have hx2_1' : s1'.readReg64 (.gpr 2#5) = BitVec.ofNat 64 sbs.length := (hcpu1.readReg64 .x2).trans hx2
      have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) := hcpu1.readReg64 _
      have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
      have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
      have hx21_1' : s1'.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) := hcpu1.readReg64 _
      have hx22_1' : s1'.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) := hcpu1.readReg64 _
      have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
      wp_conv_pre => simp only [vecHeader, ← hsp1_in]
      wp_sym_steps
      refine SepWP.done allocWriteStr_memcpy_pc (by simpa [arm64_norm] using hrun1')
        fun sm_mc hcpu_mc0 hcl_mc hnsp_mc hsym_mc => ?_
      have hcpu_mc := hcpu_mc0.1
      have ⟨hacp_0mc, hpool_0mc⟩ :=
        Io.allocCallPreserved_of_seg hcpu1_0 hcpu_mc0 hnsp_mc hsym_mc
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_0mc : A.pool lb lk s0 = A.pool lb lk sm_mc :=
        (A.pool_transport lb lk s0 sm_mc hpool_0mc).symm
      have hpc_mc : sm_mc.pc = allocMultiLib.resolve mpl "memcpy" :=
        hcpu_mc.pc_eq.trans allocWriteStr_memcpy_pc
      have hrun_mc : sm_mc.status = .Running := hcpu_mc.status_eq.trans hrun1'
      have hsp_mc_eq : sm_mc.sp = s0.sp - 48#64 :=
        hcpu_mc.sp_eq.trans (by simp [arm64_norm])
      have hlr_mc : sm_mc.readReg64 .lr =
          allocPl07.base + (reloc_call_off% allocLib07.text.relocs "memcpy" + 4#64) := by
        rw [hcpu_mc.readReg64 .lr]; simp [arm64_norm]
      have hx0_mc : sm_mc.readReg64 .x0 = ptr + BitVec.ofNat 64 bs.length := by
        rw [hcpu_mc.readReg64 .x0]; simp [arm64_norm]
      have hx1_mc : sm_mc.readReg64 .x1 = slicePtr := by
        rw [hcpu_mc.readReg64 .x1]; simpa [arm64_norm] using hx1_1'
      have hx2_mc : sm_mc.readReg64 .x2 = BitVec.ofNat 64 sbs.length := by
        rw [hcpu_mc.readReg64 .x2]; simp [arm64_norm]
      have hx19_mc : sm_mc.readReg64 (.gpr 19#5) = self := by
        rw [hcpu_mc.readReg64]; simp [arm64_norm]
      have hx20_mc : sm_mc.readReg64 (.gpr 20#5) = BitVec.ofNat 64 sbs.length := by
        rw [hcpu_mc.readReg64]; simp [arm64_norm]
      have hx21_mc : sm_mc.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length := by
        rw [hcpu_mc.readReg64]; simp [arm64_norm]
      have hgprs_mc : WriteStrHighGprs s0 sm_mc := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rw [hcpu_mc.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      have hvregs_mc : calleeSavedVRegs sm_mc = calleeSavedVRegs s0 :=
        hcpu_mc.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
      refine SepWP.weaken_pre (by
        rw [hsp1_in, hpool_eq_0mc]
        dsimp only [allocWriteStrSavedSlots, vecHeader]
        sep_entail) <|
        allocWriteStr_from_memcpy A hext7 hmemcpy hstk hcl_mc hpc_mc hrun_mc hsp0 hsp_mc_eq
          hlr_mc hx0_mc hx1_mc hx2_mc hx19_mc hx20_mc hx21_mc hgprs_mc hvregs_mc hsbs_pos hle
          fun sf _ _ hsp_f hcs_f hacp_mcf hpool_mcf hx0_f {_Pre_f} hent =>
            ⟨fun hm_out => Satisfies.mono (sepConj_mono_left (Entails.trans hent (by
              simp only [hgrew, Bool.false_eq_true, ↓reduceIte]
              rw [pure_sepConj_of_true ⟨hx0_f,
                Io.allocCallPreserved_trans hacp_0mc hacp_mcf,
                fun _ => Io.poolPreserved_trans hpool_0mc hpool_mcf⟩]
              refine Entails.trans ?_
                (sepConj_mono_right (sepConj_mono_left
                  (Entails.sepExists_right ptr (Entails.refl _))))
              rw [pure_sepConj_of_true (fun _ => rfl)]
              sep_entail))) hm_out, hsp_f, hcs_f⟩

end

end VerifiedLibraries.RustStd

