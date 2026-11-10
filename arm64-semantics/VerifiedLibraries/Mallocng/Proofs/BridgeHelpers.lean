/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.Hoare.MultiCodeROHook
public import ProofLib.Placed.Multi
public import ProofLib.SyscallModels
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Mallocng.Proofs.Defs

/-!
# Pure `mallocng` Bridge Helpers

Proves `Syscall.standard` validity for `MallocngSvcValid`, alignment and null-return layout bounds,
placement-generic `Program` lifting (`HooksUnfetched`, `ProgContainsMultiLib`,
`multiLibSubroutine_to_prog`), and specification combinators (`withExtra`,
`subroutine_ok_of_b_thunk`, `subroutine_ok_allowOom`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Syscall Validity and OOM Preservation -/

private theorem mallocngRemapRw_eq_remapRw : mallocngRemapRw = Memory.remapRw := rfl

private theorem standard_eq_execBrk (s : State) (h : s.readReg64 Reg.x8 = SYS_BRK) :
    Syscall.standard s = execBrk s := by
  unfold Syscall.standard Syscall.dispatch
  rw [h]; rfl

private theorem standard_eq_execMunmap (s : State) (h : s.readReg64 Reg.x8 = SYS_MUNMAP) :
    Syscall.standard s = execMunmap s := by
  unfold Syscall.standard Syscall.dispatch
  rw [h]; rfl

private theorem standard_eq_execMmap (s : State) (h : s.readReg64 Reg.x8 = SYS_MMAP) :
    Syscall.standard s = execMmap s := by
  unfold Syscall.standard Syscall.dispatch
  rw [h]; rfl

private theorem standard_eq_execMprotect (s : State) (h : s.readReg64 Reg.x8 = SYS_MPROTECT) :
    Syscall.standard s = execMprotect s := by
  unfold Syscall.standard Syscall.dispatch
  rw [h]; rfl

private theorem standard_eq_execMremap (s : State) (h : s.readReg64 Reg.x8 = MALLOCNG_SYS_MREMAP) :
    Syscall.standard s = execMremap s := by
  unfold Syscall.standard Syscall.dispatch
  rw [h]; rfl

theorem mallocngSvcValid_standard : MallocngSvcValid Syscall.standard := by
  intro s
  refine ⟨standard_eq_execBrk s, standard_eq_execMunmap s, standard_eq_execMmap s,
    fun h8 _ => standard_eq_execMprotect s h8, ?_⟩
  intro h8 hflags hal holdPos hnewPos hnewMax hfit hperm hanon
  rw [standard_eq_execMremap s h8]
  have hflags' : s.readReg64 Reg.x3 = MREMAP_MAYMOVE := hflags
  have holdNe : s.readReg64 Reg.x1 ≠ 0#64 := by
    intro hz; rw [hz] at holdPos; contradiction
  have hnewNe : s.readReg64 Reg.x2 ≠ 0#64 := by
    intro hz; rw [hz] at hnewPos; contradiction
  cases hmf : s.oracle.mremapFail s.oracleIdx with
  | true =>
    exact Or.inl (execMremap_enomem_of_fail s hflags' hal holdNe hnewNe hnewMax hfit hperm hanon (Or.inl hmf))
  | false =>
    cases hsan : sanitizeMmapAddr
        (s.mem.unmapNonFrozen (s.readReg64 Reg.x0) (pageAlignUp (s.readReg64 Reg.x1).toNat))
        (s.oracle.mmap s.oracleIdx)
        (pageAlignUp (s.readReg64 Reg.x2).toNat) with
    | none =>
      exact Or.inl (execMremap_enomem_of_fail s hflags' hal holdNe hnewNe hnewMax hfit hperm hanon (Or.inr hsan))
    | some newBase =>
      obtain ⟨hne, hnbAl, hnbFit, hnbMap⟩ := sanitizeMmapAddr_spec hsan
      by_cases hphys : pageAlignUp (s.readReg64 Reg.x2).toNat ≤
          s.physMemAvail + pageAlignUp (s.readReg64 Reg.x1).toNat
      · refine Or.inr (Or.inr ⟨newBase, hne, hnbAl, hnbFit, hnbMap, ?_⟩)
        rw [mallocngRemapRw_eq_remapRw]
        exact execMremap_ok s hflags' hal holdNe hnewNe hnewMax hfit hperm hanon hmf hsan hphys
      · refine Or.inr (Or.inl ⟨by omega, ?_⟩)
        exact execMremap_oom s hflags' hal holdNe hnewNe hnewMax hfit hperm hanon hmf hsan (by omega)

theorem oomCond_imp_preserved {svc : State → State} {req peak : Nat} {s0 sf : State}
    (h : MallocngOomCond svc req peak s0 sf) :
    sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-! ## Alignment and Null-Return Layout Bounds -/

theorem isPow2Align_of_toNat_pow2 {a : BitVec 64} {k : Nat} (ha : a.toNat = 2 ^ k) :
    IsPow2Align a := by
  have hkPos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  refine ⟨?_, BitVec.eq_of_toNat_eq ?_⟩
  · intro h0
    rw [h0] at ha
    simp at ha
    omega
  · have hSubNat : (a - 1#64).toNat = 2 ^ k - 1 := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (show (1#64).toNat ≤ a.toNat by
        change 1 ≤ a.toNat; omega)), ha]
      rfl
    rw [BitVec.toNat_and, ha, hSubNat, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
    rfl

theorem not_layoutFit_imp_gt_2pow62 {size align : BitVec 64}
    (hfit : ¬ MallocngLayoutFit size align) :
    2 ^ 62 < size.toNat + align.toNat := by
  unfold MallocngLayoutFit mallocngAlignedEffSize MallocngMaxAllocSize at hfit
  split at hfit <;> omega

/-! ## Placement-Generic `Program` Lifting -/

/-- Every hook entry point of `P` is non-fetchable in `Program.pureMem` across all
    frozen-preserving evolutions of `m`. -/
def HooksUnfetched (P : Program) (m : Memory) : Prop :=
  ∀ m' pc, m.KeepsFrozen m' → P.externAt? pc ≠ none →
    Program.pureMem.fetchMem m' pc = none

theorem hooksUnfetched_of_noExterns {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (m : Memory) :
    HooksUnfetched P m := by
  intro _ pc _ hne
  exact False.elim (hne (hext pc))

theorem hooksUnfetched_of_frozenNonDecode {P : Program} {m : Memory}
    (hstub : ∀ pc, P.externAt? pc ≠ none →
      m.Frozen (pc + 0#64) ∧ m.Frozen (pc + 1#64) ∧
      m.Frozen (pc + 2#64) ∧ m.Frozen (pc + 3#64) ∧
      decode (m.read32 pc) = none) :
    HooksUnfetched P m := by
  intro m' pc hkf hne
  obtain ⟨hf0, hf1, hf2, hf3, hdec⟩ := hstub pc hne
  have hr32 : m'.read32 pc = m.read32 pc := by
    simp only [Memory.read32, (hkf _ hf0).1, (hkf _ hf1).1, (hkf _ hf2).1, (hkf _ hf3).1]
  unfold Program.fetchMem
  rw [hr32, hdec]
  simp only [ite_self]

theorem hooksUnfetched_of_frozenZeroWord {P : Program} {m : Memory}
    (hstub : ∀ pc, P.externAt? pc ≠ none →
      m.Frozen (pc + 0#64) ∧ m.Frozen (pc + 1#64) ∧
      m.Frozen (pc + 2#64) ∧ m.Frozen (pc + 3#64) ∧
      m.read32 pc = 0#32) :
    HooksUnfetched P m := by
  refine hooksUnfetched_of_frozenNonDecode fun pc hne => ?_
  obtain ⟨hf0, hf1, hf2, hf3, hz⟩ := hstub pc hne
  refine ⟨hf0, hf1, hf2, hf3, ?_⟩
  rw [hz]; rfl

private theorem pureMem_externAt_none (pc : BitVec 64) :
    Program.pureMem.externAt? pc = none := rfl

/-- Lift a `Steps Program.pureMem` trace ending in a `SubroutineOutcome` status (`.Running`,
    `.Panicked`, `.Exited`, or `.OutOfMemory`, hence never `.Halted`) to `Steps P` whenever
    `P.svc = Syscall.standard` and `HooksUnfetched P s0.mem`. -/
theorem steps_prog_of_pureMem_outcome {P : Program} {s0 s sf : State}
    (hsvc : P.svc = Syscall.standard)
    (hhooks : HooksUnfetched P s0.mem)
    (h_kf : s0.mem.KeepsFrozen s.mem)
    (h_steps : Steps Program.pureMem s sf)
    (h_end : sf.status = .Running ∨ sf.status = .Panicked ∨
      (∃ c, sf.status = .Exited c) ∨ sf.status = .OutOfMemory) :
    Steps P s sf := by
  induction h_steps with
  | refl s => exact Steps.refl s
  | @step s1 s2 s3 h1 h2 ih =>
    have h_kf2 : s0.mem.KeepsFrozen s2.mem := h_kf.trans h1.keepsFrozen
    cases h1 with
    | @exec inst hr hf =>
      have hext : P.externAt? s1.pc = none := by
        cases hx : P.externAt? s1.pc with
        | none => rfl
        | some f =>
          have hnone := hhooks s1.mem s1.pc h_kf (by simp [hx])
          rw [hnone] at hf
          cases hf
      have hfP : P.fetchMem s1.mem s1.pc = some inst := by
        unfold Program.fetchMem at hf ⊢
        rw [pureMem_externAt_none s1.pc] at hf
        rwa [hext]
      have hev : Program.pureMem.evalInst inst s1 = P.evalInst inst s1 := by
        simp only [Program.evalInst, Program.pureMem, Program.pureWithSvc, Program.ofSvc, hsvc]
      have hrest := ih h_kf2 h_end
      rw [hev] at hrest
      exact Steps.step (Step.exec hr hfP) hrest
    | halt_unmapped _ _ _ =>
      have heq := Steps.from_not_running h2 (by simp)
      subst heq
      simp at h_end
    | extern _ he _ _ =>
      rw [pureMem_externAt_none] at he
      cases he
    | extern_fault _ he _ =>
      rw [pureMem_externAt_none] at he
      cases he

/-- Containment hypotheses relating `P : Program` to an `Obj.MultiPlacedLib` `lib` placed at `mpl`. -/
structure ProgContainsMultiLib (lib : Obj.MultiPlacedLib) (P : Program)
    (mpl : Obj.MultiPlacement) : Prop where
  placeable       : lib.Placeable mpl
  svc_eq          : P.svc = Syscall.standard
  codeLoaded      : ∀ m : Memory, P.CodeLoaded m → lib.CodeLoaded mpl m
  hooks_unfetched : ∀ m : Memory, P.CodeLoaded m → HooksUnfetched P m

theorem ProgContainsMultiLib.of_noExterns {lib : Obj.MultiPlacedLib} {P : Program}
    {mpl : Obj.MultiPlacement}
    (hpl : lib.Placeable mpl)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → lib.CodeLoaded mpl m)
    (hext : ∀ pc, P.externAt? pc = none) :
    ProgContainsMultiLib lib P mpl where
  placeable := hpl
  svc_eq := hsvc
  codeLoaded := hcl
  hooks_unfetched := fun m _ => hooksUnfetched_of_noExterns hext m

abbrev ProgContainsMallocng (P : Program) (mpl : Obj.MultiPlacement) : Prop :=
  ProgContainsMultiLib VerifiedLibraries.mallocngLib P mpl

/-- Lift a multi-block subroutine contract of `lib` at `mpl` under `Syscall.standard` to `P`. -/
theorem multiLibSubroutine_to_prog {S α : Type} [ToBaseSpec S α]
    {lib : Obj.MultiPlacedLib} {P : Program} {mpl : Obj.MultiPlacement}
    {fnName : String} {spec : S}
    (hP : ProgContainsMultiLib lib P mpl)
    (hbase_indep : ∀ b₁ b₂, ToBaseSpec.toSpec spec b₁ = ToBaseSpec.toSpec spec b₂)
    (hsub : ∃ i off, Obj.lookupBlockSym fnName lib.blocks = some (i, off) ∧
      subroutine_ok (lib.blockProgram mpl i (fun _ => none) (fun _ => none) Syscall.standard)
        (lib.fnAddr mpl fnName)
        (lib.withCodeLoaded mpl (ToBaseSpec.toSpec spec (mpl.base i)))) :
    subroutine_ok P (lib.fnAddr mpl fnName) (ToBaseSpec.toSpec spec P.base) := by
  obtain ⟨i, _, hfn, hok⟩ := hsub
  obtain ⟨hi, _⟩ := Obj.lookupBlockSym_some hfn
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hcode
  have hcl_all : lib.CodeLoaded mpl s0.mem := hP.codeLoaded s0.mem hcode
  have hcl_i : (lib.blockProgram mpl i (fun _ => none) (fun _ => none) Syscall.standard).CodeLoaded s0.mem :=
    hcl_all i hi
  rw [hbase_indep (mpl.base i) P.base] at hok
  have hpre_cl : s0.mem ⊨
      (lib.withCodeLoaded mpl (ToBaseSpec.toSpec spec P.base)).pre x s0 ∗ R := by
    show s0.mem ⊨ ((ToBaseSpec.toSpec spec P.base).pre x s0 ∗ ⌜lib.CodeLoaded mpl s0.mem⌝) ∗ R
    rw [sepConj_comm _ ⌜_⌝, pure_sepConj_of_true hcl_all]
    exact hpre
  rcases subroutine_ok_toPureMem_or_hookPanic (Q := fun _ => False) hok
      hpc hrun hpre_cl hsp hcl_i
      (fun pc _ _ he _ _ _ => by
        rw [Obj.MultiPlacedLib.externAt?_blockProgram_none] at he; cases he) rfl with
    ⟨sf, hsteps, hout⟩ | ⟨_, _, hfalse⟩
  · have hend : sf.status = .Running ∨ sf.status = .Panicked ∨
        (∃ c, sf.status = .Exited c) ∨ sf.status = .OutOfMemory := by
      rcases hout with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨c, hc, _⟩ | ⟨ho, _⟩
      · exact Or.inl hret.2.2
      · exact Or.inr (Or.inl hp)
      · exact Or.inr (Or.inr (Or.inl ⟨c, hc⟩))
      · exact Or.inr (Or.inr (Or.inr ho))
    have hstepsP : Steps P s0 sf :=
      steps_prog_of_pureMem_outcome hP.svc_eq (hP.hooks_unfetched s0.mem hcode)
        (Memory.KeepsFrozen.refl s0.mem) hsteps hend
    exact reaches_outcome_steps hstepsP (reaches_outcome.of_outcome hout)
  · exact False.elim hfalse

theorem mallocngMultiSubroutine_to_prog {S α : Type} [ToBaseSpec S α]
    {P : Program} {mpl : Obj.MultiPlacement} {fnName : String} {spec : S}
    (hP : ProgContainsMallocng P mpl)
    (hbase_indep : ∀ b₁ b₂, ToBaseSpec.toSpec spec b₁ = ToBaseSpec.toSpec spec b₂)
    (hsub : mallocngMultiEntryOk mpl Syscall.standard fnName spec) :
    subroutine_ok P (VerifiedLibraries.mallocngLib.fnAddr mpl fnName)
      (ToBaseSpec.toSpec spec P.base) :=
  multiLibSubroutine_to_prog hP hbase_indep hsub.2

/-! ## Extra-Invariant Framing and `B`-Thunk Combinators -/

/-- Adjoin a state-independent separation-logic invariant `extra : SepProp` to `spec.pre` and
    `spec.post`, leaving `onPanic`, `onExit`, and `onOom` unchanged. -/
def withExtra {α : Type} (extra : SepProp) (spec : Spec α) : Spec α where
  pre x s := spec.pre x s ∗ extra
  post x s0 sf := spec.post x s0 sf ∗ extra
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

theorem satisfies_drop_mid {m : Memory} {Q extra R : SepProp}
    (hm : m ⊨ Q ∗ (extra ∗ R)) : m ⊨ Q ∗ R := by
  have heq : Q ∗ (extra ∗ R) = extra ∗ (Q ∗ R) := by
    rw [← sepConj_assoc, sepConj_comm Q extra, sepConj_assoc]
  exact Satisfies.of_sep_right (heq ▸ hm)

theorem subroutine_ok_withExtra {α : Type} {P : Program} {entry : BitVec 64}
    {spec : Spec α} (extra : SepProp) (h : subroutine_ok P entry spec) :
    subroutine_ok P entry (withExtra extra spec) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _
  dsimp only [withExtra] at hpre
  rw [sepConj_assoc] at hpre
  refine subroutine_ok.mono_outcome h x (extra ∗ R) s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withExtra]
    rwa [sepConj_assoc]
  · exact Or.inr (Or.inl ⟨hp, satisfies_drop_mid hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, satisfies_drop_mid hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, satisfies_drop_mid hoom⟩))

/-- Lift a non-panicking, non-exiting `subroutine_ok` contract whose `pre`, `post`, and `onOom`
    are independent of `s0.pc` across a 1-instruction `B` thunk forwarding to `targetAddr`. -/
theorem subroutine_ok_of_b_thunk {α : Type} {P : Program} {thunkAddr targetAddr : BitVec 64}
    {spec : Spec α}
    (hf : P.fetch thunkAddr = some (.b (targetAddr - thunkAddr)))
    (hpre_pc : ∀ x (s : State) (pc' : BitVec 64), spec.pre x (s.setPC pc') = spec.pre x s :=
      by intros; rfl)
    (hpost_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.post x (s0.setPC pc') sf = spec.post x s0 sf := by intros; rfl)
    (hoom_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.onOom x (s0.setPC pc') sf = spec.onOom x s0 sf := by intros; rfl)
    (hno_pan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hno_exit : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hok : subroutine_ok P targetAddr spec) :
    subroutine_ok P thunkAddr spec := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _
  have hf0 : P.fetch s0.pc = some (.b (targetAddr - thunkAddr)) := hpc ▸ hf
  apply reaches_outcome_step hrun hf0
  have hev : P.evalInst (.b (targetAddr - thunkAddr)) s0 = s0.setPC targetAddr := by
    simp only [Program.evalInst, execInstWithSvc, hpc]
    congr 1
    bv_omega
  rw [hev]
  let s1 := s0.setPC targetAddr
  have hpre1 : s1.mem ⊨ spec.pre x s1 ∗ R := by
    dsimp only [s1]
    rw [hpre_pc]
    exact hpre
  have hpc1 := reaches_pc_of_reaches_outcome
    (oom := fun sf => sf.mem ⊨ spec.onOom x s1 sf ∗ R)
    (hok.to_outcome x R s1 rfl hrun hpre1 hsp)
    (fun sf _ hp => by rw [hno_pan] at hp; exact not_satisfies_false_sepConj hp)
    (fun _ sf _ he => by rw [hno_exit] at he; exact not_satisfies_false_sepConj he)
    (fun _ _ ho => ho)
  have hlr : s1.readReg64 Reg.lr = s0.readReg64 Reg.lr := rfl
  rw [hlr] at hpc1
  refine reaches_outcome_of_reaches_pc
    (oom := fun sf => sf.mem ⊨ spec.onOom x s0 sf ∗ R)
    (reaches_pc_mono hpc1 ?_ ?_)
    (fun _ _ ho => ho)
  · intro sf _ _ ⟨hq, hsp_cc, hcs⟩
    refine ⟨?_, hsp_cc, (CalleeSavedPreserved_setPC s0 sf targetAddr).mp hcs⟩
    dsimp only [s1] at hq
    rwa [hpost_pc] at hq
  · intro sf _ ho
    dsimp only [s1] at ho
    rwa [hoom_pc] at ho

theorem subroutine_ok_allowOom {α : Type} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry spec) :
    subroutine_ok P entry spec.allowOom := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · exact Or.inl ⟨hret, hcc, hq⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))
    dsimp only [Spec.allowOom]
    rw [pure_true_sepConj]
    exact Satisfies.drop_left hoom

theorem hookOk_allowOom {α : Type} {f : State → State} {spec : Spec α}
    (h : HookOk f spec) :
    HookOk f spec.allowOom := by
  refine HookOk.mono h
    (fun _ _ _ hm => hm)
    (fun _ _ _ _ _ hm => hm)
    (fun _ _ _ _ hm => hm)
    (fun _ _ _ _ _ hm => hm)
    (fun _ _ _ _ hm => ?_)
  dsimp only [Spec.allowOom]
  rw [pure_true_sepConj]
  exact Satisfies.drop_left hm

end VerifiedLibraries.Mallocng.Proofs
