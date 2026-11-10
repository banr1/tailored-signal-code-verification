/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.RustEntriesFine
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.HookDischarge.Libc.Memset

/-!
# `memset` Contract, Instruction Table, and Stack Helpers for `__rdl_alloc_zeroed`

Provides the `VmPreserved`-preserving `memset` contract (`allocMemsetVmSpec`), the 36-instruction
table and `WordTree` validators for `__rustc::__rdl_alloc_zeroed`, and 48-byte stack/store stepping
lemmas.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj Arm64.CType ProofLib.SepLogic ProofLib.ProgramReflection ProofLib.StdStartup
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open CryptoVerification.RustHeap (allocHookStack)
open VerifiedLibraries
open VerifiedLibraries.Mallocng hiding AllocCostModel AllocEvent MallocngCostModelIface
  MallocngCostModelSound MallocngModelEnv MallocngModelPlacedEntryContracts
  MallocngModelPostEnv MallocngStepOomCond
open VerifiedLibraries.Mallocng.Proofs (memRegion_entails_exists_pointsToBytes)
open VerifiedLibraries.Musl (memsetWords)
open VerifiedLibraries.RustStd (
  checkShimInstrsAt hookFrame_eq_stackFrame4096
)
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.HookDischarge.Libc.Memset (memset_memsetRegionSpec_ok)

/-! ## `VmPreserved`-Preserving `memset` Contract -/

/-- Total-correctness contract for `void *memset(void *ptr, int c, size_t n)` preserving both
    `AllocCallPreserved` and `VmPreserved` (`brkStart`, `brk`, `tpidrEl0`, `physMemAvail`, and
    `mem.perm`), so `A.pool lim st` transports across `memset` in `__rdl_alloc_zeroed`. -/
def allocMemsetVmSpec : Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := fun (ptr, c, n) s0 =>
    ⌜s0.readReg64 .x0 = ptr ∧
      (s0.readReg32 .x1).setWidth 8 = c ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 n ∧
      n < 2 ^ 64⌝ ∗
    memRegion ptr n
  post := fun (ptr, c, n) s0 sf =>
    ⌜sf.readReg64 .x0 = ptr ∧ AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
    (ptr ↦ₛ List.replicate n c)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem pureWordsProg_hasWords_memset (entry : BitVec 64) :
    (pureWordsProg entry memsetWords).hasWords entry memsetWords :=
  pureWordsProg_hasWords (by decide +kernel) (by
    change ((List.range memsetWords.length).all fun i =>
      (pureWordsProg 0#64 memsetWords).readWordOff (4 * i) == memsetWords[i]?) = true
    decide +kernel)

private theorem pureWordsProg_noSvcMsr_memset (entry : BitVec 64) :
    (pureWordsProg entry memsetWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  Program.allInstrs_of_code_eq (prog := pureWordsProg 0#64 memsetWords) rfl (by prove_all_instrs)

/-- Discharge `subroutine_ok P memsetAddr allocMemsetVmSpec` for any hook-free program `P`
    containing `musl` v1.2.5's AArch64 `memsetWords` (`65` words) at `memsetAddr`. -/
theorem allocMemsetVm_ok_of_hasWords (P : Program) (memsetAddr : BitVec 64)
    (h_no_ext : ∀ pc, P.externAt? pc = none)
    (h_words : P.hasWords memsetAddr memsetWords) :
    subroutine_ok P memsetAddr allocMemsetVmSpec := by
  let prog₀ := pureWordsProg memsetAddr memsetWords
  have hpure : subroutine_ok prog₀ memsetAddr
      { ProofLib.memsetRegionSpec with
        post := fun x s0 sf =>
          ⌜sf.oracle = s0.oracle ∧ sf.symtab = s0.symtab⌝ ∗
            ProofLib.memsetRegionSpec.post x s0 sf } := by
    apply subroutine_ok_of_steps_outcome
    intro x R s0 hpc hrun hpre hsp hL
    obtain ⟨sf, hsteps, hout⟩ :=
      subroutine_ok_elim_steps_outcome
        (memset_memsetRegionSpec_ok (pureWordsProg_hasWords_memset memsetAddr))
        x R s0 hpc hrun hpre hsp hL
    have horc : sf.oracle = s0.oracle :=
      Steps.oracle_eq_of_standard rfl
        (fun pc => by
          simp [pureWordsProg, Program.ofWords, Program.externAt?, Program.hookAtOff?])
        hsteps
    have hsym : sf.symtab = s0.symtab := hsteps.symtab_eq
    refine ⟨sf, hsteps, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨horc, hsym⟩, hpost⟩
    · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))
  have hlift := subroutine_ok_lift_pureWords_process hpure (pureWordsProg_noSvcMsr_memset memsetAddr)
    h_words h_no_ext
    (h_pre_mem := by intro _ s _; cases s; rfl)
    (h_post_mem := by intro _ s0 sf _ _; cases s0; cases sf; rfl)
  apply subroutine_ok.of_codeLoaded
  rintro ⟨ptr, c, n⟩ R s0 hpc hrun hpre hsp _hL
  simp only [allocMemsetVmSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
  have hn_nat : (s0.readReg64 .x2).toNat = n := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  refine hlift.mono_outcome (ptr, c, n) R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · dsimp only [ProofLib.memsetRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hn_nat, Nat.le_of_lt hlt⟩, hm⟩
  · rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      dsimp only [ProofLib.memsetRegionSpec, allocMemsetVmSpec]
      refine Entails.pure_left fun hpf => Entails.pure_left fun ⟨horc, hsym⟩ =>
        Entails.pure_left fun hx0f => ?_
      obtain ⟨hfs, htr, htp, hsig, hbrk, hbrks, hphys, hperm⟩ := hpf
      exact Entails.pure_right
        ⟨hx0f, ⟨hfs, htr, hsig, htp, hbrks, horc, hsym⟩,
          ⟨⟨hbrks, hbrk, htp⟩, hphys, hperm, FdsHiFrame.of_fs_eq hfs⟩⟩
        (Entails.refl _)
    · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

/-- Discharge `subroutine_ok P memsetAddr allocMemsetVmSpec` on any linked ELF `Program` via
    `decide +kernel` over its `WordTree`. -/
theorem allocMemsetVm_ok_of_wordTree {P : Program} {t : WordTree} {memsetAddr : BitVec 64}
    {baseOff : Nat} (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (h_no_ext : ∀ pc, P.externAt? pc = none)
    (hoff : (memsetAddr - P.base).toNat = baseOff)
    (hbnd : baseOff + 4 * memsetWords.length ≤ 2 ^ 64)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hok : checkWordsAt t baseOff memsetWords = true) :
    subroutine_ok P memsetAddr allocMemsetVmSpec :=
  allocMemsetVm_ok_of_hasWords P memsetAddr h_no_ext
    (hasWords_of_wordTree n hcode hwf hoff hbnd hstubs hsyms hok)

/-! ## Instruction Table and `WordTree` Validators -/

/-- Instruction sequence (`36` insns, `144` B) of `rustc 1.98.1` `__rustc::__rdl_alloc_zeroed` at
    `allocZeroedAddr`, tail-branching to `callocAddr` (`align ≤ 16 ∧ align ≤ size`) or calling
    `posixMemalignAddr` + `memsetAddr` (`align > 16 ∨ align > size`). -/
def rdlAllocZeroedInstrs
    (allocZeroedAddr callocAddr posixMemalignAddr memsetAddr : BitVec 64) : List Instr :=
  [ .addSubImm .W64 .SUB .sp .sp 0x30#12 false,
    .stp .W64 .x29 .x30 (.Offset .sp 0x10#64),
    .stp .W64 .x20 .x19 (.Offset .sp 0x20#64),
    .addSubImm .W64 .ADD .x29 .sp 0x10#12 false,
    .addSubImm .W64 .SUBS .xzr .x1 0x10#12 false,
    .logicalShift .W64 .ORR .x19 .xzr .x0 .LSL 0,
    .bCond .HI 0x24#64,
    .addSubShift .W64 .SUBS .xzr .x1 .x19 .LSL 0,
    .bCond .HI 0x1c#64,
    .logicalShift .W64 .ORR .x0 .xzr .x19 .LSL 0,
    .moveWide .W32 .MOVZ .x1 0x1#16 0,
    .ldp .W64 false .x20 .x19 (.Offset .sp 0x20#64),
    .ldp .W64 false .x29 .x30 (.Offset .sp 0x10#64),
    .addSubImm .W64 .ADD .sp .sp 0x30#12 false,
    .b (callocAddr - (allocZeroedAddr + 0x38#64)),
    .addSubImm .W64 .SUBS .xzr .x1 0x8#12 false,
    .moveWide .W32 .MOVZ .x8 0x8#16 0,
    .addSubImm .W64 .ADD .x0 .sp 0x8#12 false,
    .condSelect .W64 .CSEL .x1 .x1 .x8 .HI,
    .logicalShift .W64 .ORR .x2 .xzr .x19 .LSL 0,
    .str .X64 .xzr (.Offset .sp 0x8#64),
    .bl (posixMemalignAddr - (allocZeroedAddr + 0x54#64)),
    .logicalShift .W32 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x0 .xzr .xzr .LSL 0,
    .cbz .W32 true .x8 0x20#64,
    .ldr .W64 .X64 false .x20 (.Offset .sp 0x8#64),
    .cbz .W64 false .x20 0x18#64,
    .logicalShift .W64 .ORR .x0 .xzr .x20 .LSL 0,
    .logicalShift .W32 .ORR .x1 .xzr .xzr .LSL 0,
    .logicalShift .W64 .ORR .x2 .xzr .x19 .LSL 0,
    .bl (memsetAddr - (allocZeroedAddr + 0x78#64)),
    .logicalShift .W64 .ORR .x0 .xzr .x20 .LSL 0,
    .ldp .W64 false .x20 .x19 (.Offset .sp 0x20#64),
    .ldp .W64 false .x29 .x30 (.Offset .sp 0x10#64),
    .addSubImm .W64 .ADD .sp .sp 0x30#12 false,
    .ret .x30 ]

@[scoped simp] theorem rdlAllocZeroedInstrs_length (az ca pm ms : BitVec 64) :
    (rdlAllocZeroedInstrs az ca pm ms).length = 36 := rfl

private def rdlAllocZeroedRelocs : List Obj.RelocEntry :=
  [{ off := 56, kind := .jump26, sym := "calloc" },
   { off := 84, kind := .call26, sym := "posix_memalign" },
   { off := 120, kind := .call26, sym := "memset" }]

private def rdlAllocZeroedWords : List (BitVec 32) :=
  [0xd100c3ff#32, 0xa9017bfd#32, 0xa9024ff4#32, 0x910043fd#32, 0xf100403f#32, 0xaa0003f3#32,
   0x54000128#32, 0xeb13003f#32, 0x540000e8#32, 0xaa1303e0#32, 0x52800021#32, 0xa9424ff4#32,
   0xa9417bfd#32, 0x9100c3ff#32, 0x17fff4dd#32, 0xf100203f#32, 0x52800108#32, 0x910023e0#32,
   0x9a888021#32, 0xaa1303e2#32, 0xf90007ff#32, 0x97fffea4#32, 0x2a0003e8#32, 0xaa1f03e0#32,
   0x35000108#32, 0xf94007f4#32, 0xb40000d4#32, 0xaa1403e0#32, 0x2a1f03e1#32, 0xaa1303e2#32,
   0x97fff488#32, 0xaa1403e0#32, 0xa9424ff4#32, 0xa9417bfd#32, 0x9100c3ff#32, 0xd65f03c0#32]

private theorem rdlAllocZeroedInstrs_template_eq :
    (Obj.patchRelocs rdlAllocZeroedRelocs rdlAllocZeroedWords 0#64 (fun _ => 0#64)).map Arm64.decode =
      (rdlAllocZeroedInstrs 0#64 0#64 0#64 0#64).map some := by decide +kernel

/-- `WordTree` code validator for `__rustc::__rdl_alloc_zeroed` (36 instructions). -/
def checkRdlAllocZeroedCode (imgBase : BitVec 64) (t : WordTree)
    (allocZeroedAddr callocAddr posixMemalignAddr memsetAddr : BitVec 64) : Bool :=
  checkShimInstrsAt imgBase t allocZeroedAddr
    (rdlAllocZeroedInstrs allocZeroedAddr callocAddr posixMemalignAddr memsetAddr)

/-- Discharge `hasInstrs P allocZeroedAddr (rdlAllocZeroedInstrs ...)` via `decide +kernel` over `WordTree`. -/
theorem rdlAllocZeroedCode_of_wordTree {P : Program} {t : WordTree}
    {allocZeroedAddr callocAddr posixMemalignAddr memsetAddr : BitVec 64}
    (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkRdlAllocZeroedCode P.base t allocZeroedAddr callocAddr posixMemalignAddr memsetAddr = true) :
    hasInstrs P allocZeroedAddr
      (rdlAllocZeroedInstrs allocZeroedAddr callocAddr posixMemalignAddr memsetAddr) := by
  simp only [checkRdlAllocZeroedCode, checkShimInstrsAt, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hok
  exact hasInstrs_of_wordTree n hcode hwf hok.1.1 hok.1.2 hext hovr hok.2

/-- `WordTree` validator for the 1-instruction `B` thunk `__rust_alloc_zeroed → __rdl_alloc_zeroed`. -/
def checkRdlAllocZeroedThunk (imgBase : BitVec 64) (t : WordTree)
    (thunkAddr targetAddr : BitVec 64) : Bool :=
  checkShimInstrsAt imgBase t thunkAddr [ .b (targetAddr - thunkAddr) ]

/-- Discharge `hasInstrs P thunkAddr [ .b (targetAddr - thunkAddr) ]` via `decide +kernel` over `WordTree`. -/
theorem rdlAllocZeroedThunk_of_wordTree {P : Program} {t : WordTree}
    {thunkAddr targetAddr : BitVec 64}
    (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkRdlAllocZeroedThunk P.base t thunkAddr targetAddr = true) :
    hasInstrs P thunkAddr [ .b (targetAddr - thunkAddr) ] := by
  simp only [checkRdlAllocZeroedThunk, checkShimInstrsAt, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hok
  exact hasInstrs_of_wordTree n hcode hwf hok.1.1 hok.1.2 hext hovr hok.2

/-! ## Stack and Store Helpers -/

namespace AllocZeroedHelpers

attribute [local simp] Memory.perm_write8 Memory.perm_write16 Memory.perm_write32
  Memory.perm_write64 Memory.perm_writeBytes

@[scoped simp] theorem physMemAvail_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).physMemAvail = s.physMemAvail := by cases s; rfl

@[scoped simp] theorem physMemAvail_advancePC (s : State) :
    s.advancePC.physMemAvail = s.physMemAvail := by cases s; rfl

@[scoped simp] theorem physMemAvail_setPState (s : State) (ps : PState) :
    (s.setPState ps).physMemAvail = s.physMemAvail := by cases s; rfl

@[scoped simp] theorem physMemAvail_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).physMemAvail = s.physMemAvail := by cases s; cases r <;> rfl

@[scoped simp] theorem physMemAvail_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).physMemAvail = s.physMemAvail := physMemAvail_writeReg64 s r _

@[scoped simp] theorem physMemAvail_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).physMemAvail = s.physMemAvail := physMemAvail_writeReg64 s r _

@[scoped simp] theorem physMemAvail_setMem (s : State) (m : Memory) :
    (s.setMem m).physMemAvail = s.physMemAvail := by cases s; rfl

@[scoped simp] theorem perm_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).mem.perm = s.mem.perm := by cases s; rfl

@[scoped simp] theorem perm_advancePC (s : State) :
    s.advancePC.mem.perm = s.mem.perm := by cases s; rfl

@[scoped simp] theorem perm_setPState (s : State) (ps : PState) :
    (s.setPState ps).mem.perm = s.mem.perm := by cases s; rfl

@[scoped simp] theorem perm_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem.perm = s.mem.perm := by cases s; cases r <;> rfl

@[scoped simp] theorem perm_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).mem.perm = s.mem.perm := perm_writeReg64 s r _

@[scoped simp] theorem perm_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).mem.perm = s.mem.perm := perm_writeReg64 s r _

@[scoped simp] theorem perm_setMem (s : State) (m : Memory) :
    (s.setMem m).mem.perm = m.perm := by cases s; rfl

theorem step_str64_perm {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 64}
    (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .X64 rt addr) := hpc.symm ▸ hfetch
  let m' := s.mem.write64 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea _ = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .X64 rt addr) s = s'.setMem m' := by
    rw [evalInst_eq_execInst_of_not_isSvc0 prog rfl s, ← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write64 s.mem ea val)) hm'

theorem step_stp64_perm {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1)
    (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc
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
    rw [evalInst_eq_execInst_of_not_isSvc0 prog rfl s, ← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))) hm2

scoped macro "wp_str64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_str64_perm $hf
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_sep_access
  · wp_focus_close wp_norm_lhs
  intro $m $hm
  try wp_norm_state))

scoped macro "wp_stp64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_stp64_perm $hf
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_sep_access
  · wp_focus_close wp_sep_access
  · wp_focus_close wp_norm_lhs
  intro $m $hm
  try wp_norm_state))

theorem vmPreserved_of_eq {s0 s1 : State}
    (hbs : s1.brkStart = s0.brkStart) (hbrk : s1.brk = s0.brk)
    (htp : s1.tpidrEl0 = s0.tpidrEl0) (hphys : s1.physMemAvail = s0.physMemAvail)
    (hperm : s1.mem.perm = s0.mem.perm)
    (hfs : s1.fs = s0.fs := by simp [arm64_norm]) :
    VmPreserved s0 s1 :=
  ⟨⟨hbs, hbrk, htp⟩, hphys, fun a => congrFun hperm a, FdsHiFrame.of_fs_eq hfs⟩

theorem vmPreserved_trans {s0 s1 s2 : State}
    (h01 : VmPreserved s0 s1) (h12 : VmPreserved s1 s2) :
    VmPreserved s0 s2 :=
  h01.trans h12

theorem oomPreserved_of_allocCallPreserved {s0 s1 sf : State}
    (h01 : AllocCallPreserved s0 s1) (h1f : OomPreserved s1 sf) :
    OomPreserved s0 sf :=
  ⟨h1f.1.trans h01.1, h1f.2.1.trans h01.2.1, h1f.2.2.trans h01.2.2.1⟩

theorem allocCallPreserved_of_eq {s0 sf : State}
    (hfs : sf.fs = s0.fs) (htr : sf.trace = s0.trace) (hsig : sf.sigActions = s0.sigActions)
    (htp : sf.tpidrEl0 = s0.tpidrEl0) (hbs : sf.brkStart = s0.brkStart)
    (horc : sf.oracle = s0.oracle) (hsym : sf.symtab = s0.symtab) :
    AllocCallPreserved s0 sf :=
  ⟨hfs, htr, hsig, htp, hbs, horc, hsym⟩

theorem sixteen_dvd_max16_of_layoutOk {sz al : Nat} (h : RustLayoutOk sz al) :
    16 ∣ max al 16 := by
  obtain ⟨_, ⟨k, rfl⟩, _⟩ := h.1
  by_cases hk : k ≤ 4
  · have hle : 2 ^ k ≤ 16 := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    simpa only [Nat.max_eq_right hle] using Nat.dvd_refl 16
  · have hge : 16 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ k)
    rw [Nat.max_eq_left hge, show k = 4 + (k - 4) by omega, Nat.pow_add]
    exact Nat.dvd_mul_right 16 (2 ^ (k - 4))

theorem calleeSavedPreserved_trans {s0 s1 s2 : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 :=
  VerifiedLibraries.Mallocng.Proofs.calleeSavedPreserved_trans h01 h12

theorem stackAt_eq_hookFrame (sp : BitVec 64) :
    stackAt sp allocHookStack = Rust.hookFrame sp := rfl

theorem packLiveM {M : AllocCostModel} {I : MallocngCostModelIface M}
    (γ : GhostName) {p : BitVec 64} {n al : Nat}
    (hpNe : p ≠ 0#64) (hAl : al ∣ p.toNat) (h16 : 16 ∣ p.toNat)
    (hFit : p.toNat + n < 2 ^ 64) (hLay : RustLayoutOk n al) :
    I.BlockM γ p n (max al 16) ⊢ mallocngLiveM M I γ p n al := by
  unfold mallocngLiveM
  rw [sepConj_comm]
  exact Entails.pure_right ⟨hpNe, hAl, h16, hFit, hLay⟩ (Entails.refl _)

theorem packLiveM_16 {M : AllocCostModel} {I : MallocngCostModelIface M}
    (γ : GhostName) {p : BitVec 64} {n al : Nat}
    (hAl16 : al ≤ 16) (hpNe : p ≠ 0#64) (hAl : al ∣ p.toNat) (h16 : 16 ∣ p.toNat)
    (hFit : p.toNat + n < 2 ^ 64) (hLay : RustLayoutOk n al) :
    I.BlockM γ p n 16 ⊢ mallocngLiveM M I γ p n al := by
  have hm : max al 16 = 16 := Nat.max_eq_right hAl16
  rw [← hm]
  exact packLiveM γ hpNe hAl h16 hFit hLay

theorem memRegion8_entails_pointsTo64 (a : BitVec 64) :
    memRegion a 8 ⊢ ∃∗ w : BitVec 64, a ↦₆₄ w := by
  refine Entails.trans (memRegion_entails_exists_pointsToBytes 8 a (by decide)) ?_
  refine Entails.sepExists_elim fun bs => Entails.pure_left fun hlen => ?_
  have htake : (bs.drop 0).take 8 = bs := by
    simp [List.take_of_length_le (by omega : bs.length ≤ 8)]
  have heq := pointsToBytes_take8_eq_pointsTo64 a bs 0 (by omega)
  rw [htake] at heq
  rw [heq]
  exact Entails.sepExists_right _ (Entails.refl _)

theorem hookFrame_eq_stack48_1024 (sp : BitVec 64) :
    Rust.hookFrame sp =
      (stackFrameAt sp 48 ∗
        (stackFrameAt (sp - 48#64) mallocngStackBytes ∗
          stackFrameAt (sp - 48#64 - 1024#64) 3024)) := by
  rw [hookFrame_eq_stackFrame4096 sp,
      show (4096 : Nat) = 48 + 4048 from rfl,
      stackFrameAt_split sp 48 4048 (by decide),
      show (4048 : Nat) = 1024 + 3024 from rfl,
      stackFrameAt_split (sp - 48#64) 1024 3024 (by decide)]

theorem stackFrameAt48_eq (sp : BitVec 64) :
    stackFrameAt sp 48 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
        ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
        ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]

theorem pack_stack48 (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
     ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
     ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢ stackFrameAt sp 48 := by
  rw [stackFrameAt48_eq sp]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.refl _))))))

theorem repack_hookFrame_48 (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
     ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
     ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ∗
    (stackFrameAt (sp - 48#64) mallocngStackBytes ∗
     stackFrameAt (sp - 48#64 - 1024#64) 3024) ⊢
      Rust.hookFrame sp := by
  rw [hookFrame_eq_stack48_1024 sp]
  exact sepConj_mono_left (pack_stack48 sp w0 w1 w2 w3 w4 w5)

theorem spAligned_sub48 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 48#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_robdd

end AllocZeroedHelpers

end LibsignalBinary.Heap.Fine
