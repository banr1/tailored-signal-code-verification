/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.MultiCodeROHook

/-!
# Determinism Bridges for MultiPlacedLib Subroutine Hooks

Eliminates `Classical.choose` in `Arm64.Obj.MultiPlacedLib.codeROSubroutineHook` from a concrete
`Arm64.StepsUntil` witness ending in `Arm64.SubroutineStop`, and proves that `loadMultiCodeMem`
and `restoreMultiCodeMem` act as the identity when `lib.CodeLoaded mpl` holds on caller memory.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.SubroutineChoiceBridge

private theorem memory_ext {m1 m2 : Arm64.Memory} (h : ∀ a, m1.cells a = m2.cells a) :
    m1 = m2 := by
  cases m1
  cases m2
  congr 1
  exact funext h

private theorem add_ofNat_sub_toNat (base a : BitVec 64) :
    base + BitVec.ofNat 64 (a - base).toNat = a := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

private theorem codeLoaded_at_findCodeBlock {lib : Arm64.Obj.MultiPlacedLib}
    {mpl : Arm64.Obj.MultiPlacement} {m : Arm64.Memory} {a : BitVec 64} {k : Nat}
    (hcl : lib.CodeLoaded mpl m)
    (hk : lib.findCodeBlock mpl a = some k) :
    ∃ hin : (a - mpl.base k).toNat < (lib.blockPatched mpl k).length,
      m.read8 a = (lib.blockPatched mpl k)[(a - mpl.base k).toNat]'hin ∧
      m.perm a = some Arm64.Perm.rx ∧
      m.isLazyFree a = false := by
  have hf : (List.range lib.blocks.length).find?
      (fun j => decide (Arm64.InRegion (mpl.base j) (lib.blockPatched mpl j).length a)) =
      some k := hk
  have hk_lt : k < lib.blocks.length := List.mem_range.mp (List.mem_of_find?_eq_some hf)
  have hdec := List.find?_some hf
  have hin : (a - mpl.base k).toNat < (lib.blockPatched mpl k).length :=
    of_decide_eq_true hdec
  have hprog : (lib.blockProgram mpl k).CodeLoaded m := hcl k hk_lt
  obtain ⟨_, _, hbytes⟩ := Arm64.Program.codeLoaded_iff.mp hprog
  have hba : (lib.blockProgram mpl k).base + BitVec.ofNat 64 (a - mpl.base k).toNat = a :=
    add_ofNat_sub_toNat (mpl.base k) a
  obtain ⟨hrd, hperm, hlf⟩ := hbytes (a - mpl.base k).toNat hin
  rw [hba] at hrd hperm hlf
  exact ⟨hin, hrd, hperm, hlf⟩

theorem step_deterministic {prog : Arm64.Program} {s s1 s2 : Arm64.State}
    (h1 : Arm64.Step prog s s1) (h2 : Arm64.Step prog s s2) : s1 = s2 :=
  Arm64.Step.deterministic h1 h2

theorem stepsUntil_deterministic {prog : Arm64.Program} {stop : Arm64.State → Prop}
    {s0 s1 s2 : Arm64.State}
    (h1 : Arm64.StepsUntil prog stop s0 s1) (hs1 : stop s1)
    (h2 : Arm64.StepsUntil prog stop s0 s2) (hs2 : stop s2) : s1 = s2 :=
  Arm64.StepsUntil.deterministic h1 hs1 h2 hs2

open Classical in
/-- Evaluates `lib.codeROSubroutineHook` to `multiCodeROHookExit` given a concrete `StepsUntil`
run ending at a `SubroutineStop` state `sf'`. -/
theorem codeROSubroutineHook_eq_of_stepsUntil
    (lib : Arm64.Obj.MultiPlacedLib) (mpl : Arm64.Obj.MultiPlacement)
    (fnName : String) (i off : Nat)
    (hlook : Arm64.Obj.lookupBlockSym fnName lib.blocks = some (i, off))
    (externs overrides : String → Option (Arm64.State → Arm64.State))
    (svc : Arm64.State → Arm64.State)
    {s0 sf' : Arm64.State}
    (hsteps : Arm64.StepsUntil (lib.blockProgram mpl i externs overrides svc)
      (Arm64.SubroutineStop (Arm64.multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0))
      (Arm64.multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) sf')
    (hstop : Arm64.SubroutineStop
      (Arm64.multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) sf') :
    lib.codeROSubroutineHook mpl fnName externs overrides svc s0 =
      Arm64.multiCodeROHookExit lib mpl i s0 sf' := by
  have hex : ∃ sf, Arm64.StepsUntil (lib.blockProgram mpl i externs overrides svc)
      (Arm64.SubroutineStop (Arm64.multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0))
      (Arm64.multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) sf ∧
      Arm64.SubroutineStop
        (Arm64.multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) sf :=
    ⟨sf', hsteps, hstop⟩
  unfold Arm64.Obj.MultiPlacedLib.codeROSubroutineHook
  rw [hlook]
  dsimp only
  simp only [hex, ↓reduceDIte]
  congr 1
  exact stepsUntil_deterministic (Classical.choose_spec hex).1 (Classical.choose_spec hex).2
    hsteps hstop

theorem loadMultiCodeMem_eq_self {lib : Arm64.Obj.MultiPlacedLib} {mpl : Arm64.Obj.MultiPlacement}
    {m : Arm64.Memory} (hcl : lib.CodeLoaded mpl m) :
    Arm64.loadMultiCodeMem lib mpl m = m := by
  apply memory_ext
  intro a
  unfold Arm64.loadMultiCodeMem
  dsimp (config := { zetaHave := true }) only
  split
  · rename_i k hk
    obtain ⟨_, hrd, hperm, hlf⟩ := codeLoaded_at_findCodeBlock hcl hk
    rcases hcell : m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, b⟩
    · simp [Arm64.Memory.perm, hcell] at hperm
    · simp [Arm64.Memory.perm, hcell] at hperm
    · simp only [Arm64.Memory.perm, Arm64.Perm.rwx, Arm64.Perm.rx, hcell, Option.some.injEq,
        Arm64.Perm.mk.injEq] at hperm
      simp only [Arm64.Memory.isLazyFree, hcell] at hlf
      simp only [Arm64.Memory.read8, hcell] at hrd
      rcases hperm with ⟨rfl, rfl, rfl, -, -⟩
      subst hlf hrd
      simp [Arm64.Memory.isAnon, hcell, Arm64.Perm.rx]
  · rfl

theorem restoreMultiCodeMem_eq_right {lib : Arm64.Obj.MultiPlacedLib} {mpl : Arm64.Obj.MultiPlacement}
    {m0 mf : Arm64.Memory} (hcl : lib.CodeLoaded mpl m0) (hkf : m0.KeepsFrozen mf) :
    Arm64.restoreMultiCodeMem lib mpl m0 mf = mf := by
  apply memory_ext
  intro a
  unfold Arm64.restoreMultiCodeMem
  dsimp only
  split
  · rename_i k hk
    obtain ⟨_, _, hperm0, _⟩ := codeLoaded_at_findCodeBlock hcl hk
    have hfr : m0.Frozen a := by
      unfold Arm64.Memory.Frozen
      rw [hperm0]
      rfl
    obtain ⟨hrd, hp, hlf, han⟩ := hkf a hfr
    have hpermf : mf.perm a = some Arm64.Perm.rx := hp.trans hperm0
    rcases hc0 : m0.cells a with _ | ⟨_ | ⟨r0, w0, x0, lf0, an0⟩, b0⟩
    · simp [Arm64.Memory.perm, hc0] at hperm0
    · simp [Arm64.Memory.perm, hc0] at hperm0
    · rcases hcf : mf.cells a with _ | ⟨_ | ⟨rf, wf, xf, lff, anf⟩, bf⟩
      · simp [Arm64.Memory.perm, hcf] at hpermf
      · simp [Arm64.Memory.perm, hcf] at hpermf
      · simp only [Arm64.Memory.perm, Arm64.Perm.rwx, Arm64.Perm.rx, hc0, Option.some.injEq,
          Arm64.Perm.mk.injEq] at hperm0
        simp only [Arm64.Memory.perm, Arm64.Perm.rwx, Arm64.Perm.rx, hcf, Option.some.injEq,
          Arm64.Perm.mk.injEq] at hpermf
        simp only [Arm64.Memory.read8, hc0, hcf] at hrd
        simp only [Arm64.Memory.isLazyFree, hc0, hcf] at hlf
        simp only [Arm64.Memory.isAnon, hc0, hcf] at han
        rcases hperm0 with ⟨rfl, rfl, rfl, -, -⟩
        rcases hpermf with ⟨rfl, rfl, rfl, -, -⟩
        subst hrd hlf han
        rfl
  · rfl

/-- Decidable Boolean check for `Arm64.SubroutineStop s0 s` from `lr0 = s0.readReg64 .lr` and
`sp0 = s0.sp`. -/
def isSubroutineStopB (lr0 sp0 : BitVec 64) (st : Arm64.ExecStatus) (pc sp : BitVec 64) : Bool :=
  match st with
  | .Running => (pc == lr0) && (sp == sp0)
  | .Panicked | .Exited _ | .OutOfMemory => true
  | _ => false

theorem isSubroutineStopB_eq_true_iff (s0 s : Arm64.State) :
    isSubroutineStopB (s0.readReg64 .lr) s0.sp s.status s.pc s.sp = true ↔
      Arm64.SubroutineStop s0 s := by
  unfold isSubroutineStopB Arm64.SubroutineStop Arm64.Returned
  cases s.status <;> simp

theorem multiCodeROHookEntry_eq_of_codeLoaded {lib : Arm64.Obj.MultiPlacedLib}
    {mpl : Arm64.Obj.MultiPlacement} {i : Nat} {entry_pc : BitVec 64} {s0 : Arm64.State}
    (hcl : lib.CodeLoaded mpl s0.mem) :
    Arm64.multiCodeROHookEntry lib mpl i entry_pc s0 =
      (s0.writeReg64 .lr (mpl.base i + 1#64)).setPC entry_pc := by
  unfold Arm64.multiCodeROHookEntry
  rw [loadMultiCodeMem_eq_self hcl]
  cases s0
  rfl

theorem multiCodeROHookExit_eq_of_codeLoaded {lib : Arm64.Obj.MultiPlacedLib}
    {mpl : Arm64.Obj.MultiPlacement} {i : Nat} {s0 sf' : Arm64.State}
    (hcl : lib.CodeLoaded mpl s0.mem) (hkf : s0.mem.KeepsFrozen sf'.mem) :
    Arm64.multiCodeROHookExit lib mpl i s0 sf' =
      (let lr0 := s0.readReg64 .lr
       let sf1 := if sf'.pc = mpl.base i + 1#64 ∧ sf'.status = .Running then sf'.setPC lr0 else sf'
       sf1.writeReg64 .lr lr0) := by
  unfold Arm64.multiCodeROHookExit
  rw [restoreMultiCodeMem_eq_right hcl hkf]
  dsimp only
  split <;> (cases sf'; rfl)

end Symbolic.BugInjection.Proofs.CliExec.SubroutineChoiceBridge
