/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.SubroutineHook
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model

/-!
# Read-Only Multi-Block Subroutine Hooks

Lifts verified `Obj.MultiPlacedLib` subroutines to state-transformer hooks (`HookOk`) backed by
read-only byte-slice ownership `lib.codeRO mpl` (`↦ᵣ`) in `spec.pre`, without requiring `PermsRX`,
`CodeLoaded s0.mem`, or `SepProp.NoRO`. Defines the multi-block overlay and restoration primitives
`loadMultiCodeMem` and `restoreMultiCodeMem`, the induced hook `codeROSubroutineHook`, and the
lifting theorems `subroutineHook_ok_of_multiCodeRO_at`, `subroutineHook_ok_of_multiCodeRO_framed`,
and `subroutineHook_ok_of_multiCodeRO`.
-/

@[expose] public section

/-- Relocated byte sequence of block `k` of `lib` under placement `mpl`. -/
def Arm64.Obj.MultiPlacedLib.blockPatched (lib : Arm64.Obj.MultiPlacedLib)
    (mpl : Arm64.Obj.MultiPlacement) (k : Nat) : List (BitVec 8) :=
  (lib.blockLib k).text.patched (lib.blockPlacement mpl k)

/-- First block index `k < lib.blocks.length` whose relocated code region under `mpl` contains `a`
    (`none` if `a` lies outside all code blocks of `lib`). Under `lib.Placeable mpl`, block regions
    are pairwise disjoint so at most one block contains `a`. -/
def Arm64.Obj.MultiPlacedLib.findCodeBlock (lib : Arm64.Obj.MultiPlacedLib)
    (mpl : Arm64.Obj.MultiPlacement) (a : BitVec 64) : Option Nat :=
  (List.range lib.blocks.length).find? fun k =>
    decide (Arm64.InRegion (mpl.base k) (lib.blockPatched mpl k).length a)

/-- Overlay all blocks `k < lib.blocks.length` of `lib` with `some Perm.rx` and their relocated
    code bytes `lib.blockPatched mpl k` in `m`, leaving all addresses outside `lib`'s blocks
    unchanged. -/
def Arm64.loadMultiCodeMem (lib : Arm64.Obj.MultiPlacedLib) (mpl : Arm64.Obj.MultiPlacement)
    (m : Arm64.Memory) : Arm64.Memory :=
  ⟨fun a =>
    match h : lib.findCodeBlock mpl a with
    | some k =>
      have hf : (List.range lib.blocks.length).find?
          (fun j => decide (Arm64.InRegion (mpl.base j) (lib.blockPatched mpl j).length a)) =
          some k := h
      have hd := List.find?_some hf
      have hin : Arm64.InRegion (mpl.base k) (lib.blockPatched mpl k).length a :=
        of_decide_eq_true hd
      some (some { Arm64.Perm.rx with anon := m.isAnon a },
        (lib.blockPatched mpl k)[(a - mpl.base k).toNat]'hin)
    | none => m.cells a⟩

/-- Restore `m0.cells` across all code blocks of `lib` under `mpl`, keeping `mf.cells` outside
    `lib`'s code blocks. -/
def Arm64.restoreMultiCodeMem (lib : Arm64.Obj.MultiPlacedLib) (mpl : Arm64.Obj.MultiPlacement)
    (m0 mf : Arm64.Memory) : Arm64.Memory :=
  ⟨fun a =>
    match lib.findCodeBlock mpl a with
    | some _ => m0.cells a
    | none => mf.cells a⟩

/-- Entry state for running block `i` of `lib` at `entry_pc` under `mpl`: sets `lr := mpl.base i + 1`,
    `pc := entry_pc`, and overlays all blocks of `lib` via `loadMultiCodeMem`. -/
def Arm64.multiCodeROHookEntry (lib : Arm64.Obj.MultiPlacedLib) (mpl : Arm64.Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : Arm64.State) : Arm64.State :=
  ((s0.writeReg64 .lr (mpl.base i + 1#64)).setPC entry_pc).setMem
    (Arm64.loadMultiCodeMem lib mpl s0.mem)

/-- Exit state restoring caller `lr`, return `pc` (when `sf'` stopped at the sentinel
    `mpl.base i + 1`), and code-block memory cells via `restoreMultiCodeMem`. -/
def Arm64.multiCodeROHookExit (lib : Arm64.Obj.MultiPlacedLib) (mpl : Arm64.Obj.MultiPlacement)
    (i : Nat) (s0 sf' : Arm64.State) : Arm64.State :=
  let lr0 := s0.readReg64 .lr
  let sf1 := if sf'.pc = mpl.base i + 1#64 ∧ sf'.status = .Running then sf'.setPC lr0 else sf'
  (sf1.writeReg64 .lr lr0).setMem (Arm64.restoreMultiCodeMem lib mpl s0.mem sf'.mem)

open Classical in
/-- State-transformer hook (`State → State`) induced by exported subroutine `fnName` of `lib` under
    placement `mpl`, overlaying all blocks via `loadMultiCodeMem` on entry and restoring caller
    code-block cells via `restoreMultiCodeMem` on exit so `lib.codeRO mpl` (`↦ᵣ`) suffices in
    `spec.pre` without `PermsRX` or `CodeLoaded s0.mem`. -/
noncomputable def Arm64.Obj.MultiPlacedLib.codeROSubroutineHook (lib : Arm64.Obj.MultiPlacedLib)
    (mpl : Arm64.Obj.MultiPlacement) (fnName : String)
    (externs : String → Option (Arm64.State → Arm64.State) := fun _ => none)
    (overrides : String → Option (Arm64.State → Arm64.State) := fun _ => none)
    (svc : Arm64.State → Arm64.State := Arm64.Syscall.standard) :
    Arm64.State → Arm64.State :=
  match Arm64.Obj.lookupBlockSym fnName lib.blocks with
  | some (i, _) => fun s0 =>
    let prog := lib.blockProgram mpl i externs overrides svc
    let s0' := Arm64.multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0
    if h : ∃ sf', Arm64.StepsUntil prog (Arm64.SubroutineStop s0') s0' sf' ∧
        Arm64.SubroutineStop s0' sf' then
      Arm64.multiCodeROHookExit lib mpl i s0 (Classical.choose h)
    else
      s0
  | none => id

/-- Alias for `Arm64.Obj.MultiPlacedLib.codeROSubroutineHook`. -/
noncomputable abbrev Arm64.multiCodeROSubroutineHook :=
  @Arm64.Obj.MultiPlacedLib.codeROSubroutineHook

/-- Default hook contract bundling `lib.codeRO mpl` (`↦ᵣ`) with
    `ToBaseSpec.toSpec (spec mpl) (mpl.base i)` across `multiCodeROHookEntry` /
    `multiCodeROHookExit`, returning `lib.codeRO mpl` in `post` and forwarding `onOom`. -/
def Arm64.Spec.codeROMultiSubroutineHook {S β : Type} [Arm64.ToBaseSpec S β]
    (lib : Arm64.Obj.MultiPlacedLib) (mpl : Arm64.Obj.MultiPlacement)
    (fnName : String) (spec : Arm64.Obj.MultiPlacement → S) :
    Arm64.Spec β :=
  let i := lib.fnBlockIdx fnName
  let inner := Arm64.ToBaseSpec.toSpec (spec mpl) (mpl.base i)
  { pre := fun y s0 =>
      lib.codeRO mpl ∗
        inner.pre y (Arm64.multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0)
    post := fun y s0 sf =>
      ∃∗ sf',
        ⌜sf = Arm64.multiCodeROHookExit lib mpl i s0 sf' ∧ lib.CodeLoaded mpl sf'.mem⌝ ∗
          (lib.codeRO mpl ∗
            inner.post y (Arm64.multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) sf')
    onOom := fun y s0 sf =>
      ∃∗ sf',
        ⌜sf = Arm64.multiCodeROHookExit lib mpl i s0 sf'⌝ ∗
          inner.onOom y (Arm64.multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) sf' }

/-- Projection-friendly alias for `Arm64.Spec.codeROMultiSubroutineHook`. -/
abbrev Arm64.Obj.MultiPlacedLib.codeROSubroutineHookSpec :=
  @Arm64.Spec.codeROMultiSubroutineHook

namespace ProofLib

open Arm64

/-! ## State Projections for `multiCodeROHookEntry` and `multiCodeROHookExit` -/

@[simp]
theorem multiCodeROHookEntry_pc (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).pc = entry_pc := rfl

@[simp]
theorem multiCodeROHookEntry_sp (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).sp = s0.sp := rfl

@[simp]
theorem multiCodeROHookEntry_spAligned (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).spAligned = s0.spAligned := rfl

@[simp]
theorem multiCodeROHookEntry_status (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).status = s0.status := rfl

@[simp]
theorem multiCodeROHookEntry_mem (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).mem = loadMultiCodeMem lib mpl s0.mem := rfl

@[simp]
theorem multiCodeROHookEntry_tpidrEl0 (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).tpidrEl0 = s0.tpidrEl0 := rfl

@[simp]
theorem multiCodeROHookEntry_brk (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).brk = s0.brk := rfl

@[simp]
theorem multiCodeROHookEntry_brkStart (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).brkStart = s0.brkStart := rfl

@[simp]
theorem multiCodeROHookEntry_fs (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).fs = s0.fs := rfl

@[simp]
theorem multiCodeROHookEntry_trace (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).trace = s0.trace := rfl

@[simp]
theorem multiCodeROHookEntry_symtab (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).symtab = s0.symtab := rfl

@[simp]
theorem multiCodeROHookEntry_sigActions (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).sigActions = s0.sigActions := rfl

@[simp]
theorem multiCodeROHookEntry_physMemAvail (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).physMemAvail = s0.physMemAvail := rfl

@[simp]
theorem multiCodeROHookEntry_oracle (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).oracle = s0.oracle := rfl

@[simp]
theorem multiCodeROHookEntry_oracleIdx (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).oracleIdx = s0.oracleIdx := rfl

@[simp]
theorem multiCodeROHookEntry_readReg64_lr (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).readReg64 .lr = mpl.base i + 1#64 := rfl

@[simp]
theorem multiCodeROHookEntry_readReg64 (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) (r : Reg) (hr : r ≠ .lr := by decide) :
    (multiCodeROHookEntry lib mpl i entry_pc s0).readReg64 r = s0.readReg64 r := by
  simp [multiCodeROHookEntry, hr]

@[simp, arm64_norm]
theorem calleeSavedVRegs_multiCodeROHookEntry (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entry_pc : BitVec 64) (s0 : State) :
    calleeSavedVRegs (multiCodeROHookEntry lib mpl i entry_pc s0) = calleeSavedVRegs s0 := by
  cases s0; rfl

@[simp]
theorem multiCodeROHookExit_mem (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').mem = restoreMultiCodeMem lib mpl s0.mem sf'.mem := rfl

@[simp]
theorem multiCodeROHookExit_sp (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').sp = sf'.sp := by
  unfold multiCodeROHookExit; dsimp only; split <;> rfl

@[simp]
theorem multiCodeROHookExit_status (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').status = sf'.status := by
  unfold multiCodeROHookExit; dsimp only; split <;> rfl

@[simp]
theorem multiCodeROHookExit_tpidrEl0 (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').tpidrEl0 = sf'.tpidrEl0 := by
  unfold multiCodeROHookExit; dsimp only; split <;> rfl

@[simp]
theorem multiCodeROHookExit_brk (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').brk = sf'.brk := by
  unfold multiCodeROHookExit; dsimp only; split <;> rfl

@[simp]
theorem multiCodeROHookExit_brkStart (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').brkStart = sf'.brkStart := by
  unfold multiCodeROHookExit; dsimp only; split <;> rfl

@[simp]
theorem multiCodeROHookExit_fs (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').fs = sf'.fs := by
  unfold multiCodeROHookExit; dsimp only; split <;> rfl

@[simp]
theorem multiCodeROHookExit_trace (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').trace = sf'.trace := by
  unfold multiCodeROHookExit; dsimp only; split <;> rfl

@[simp]
theorem multiCodeROHookExit_symtab (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').symtab = sf'.symtab := by
  unfold multiCodeROHookExit; dsimp only; split <;> rfl

@[simp]
theorem multiCodeROHookExit_sigActions (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').sigActions = sf'.sigActions := by
  unfold multiCodeROHookExit; dsimp only; split <;> rfl

@[simp]
theorem multiCodeROHookExit_physMemAvail (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').physMemAvail = sf'.physMemAvail := by
  unfold multiCodeROHookExit; dsimp only; split <;> rfl

@[simp]
theorem multiCodeROHookExit_oracle (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').oracle = sf'.oracle := by
  unfold multiCodeROHookExit; dsimp only; split <;> rfl

@[simp]
theorem multiCodeROHookExit_oracleIdx (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').oracleIdx = sf'.oracleIdx := by
  unfold multiCodeROHookExit; dsimp only; split <;> rfl

@[simp]
theorem multiCodeROHookExit_readReg64_lr (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').readReg64 .lr = s0.readReg64 .lr := by
  unfold multiCodeROHookExit; dsimp only; split <;> simp

@[simp]
theorem multiCodeROHookExit_readReg64 (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) (r : Reg) (hr : r ≠ .lr := by decide) :
    (multiCodeROHookExit lib mpl i s0 sf').readReg64 r = sf'.readReg64 r := by
  unfold multiCodeROHookExit; dsimp only; split <;> simp [hr]

@[simp, arm64_norm]
theorem calleeSavedVRegs_multiCodeROHookExit (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    calleeSavedVRegs (multiCodeROHookExit lib mpl i s0 sf') = calleeSavedVRegs sf' := by
  unfold multiCodeROHookExit; dsimp only; split <;> (cases sf'; rfl)

theorem multiCodeROHookExit_returned {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    {i : Nat} {entry_pc : BitVec 64} {s0 sf' : State}
    (hret : Returned (multiCodeROHookEntry lib mpl i entry_pc s0) sf') :
    Returned s0 (multiCodeROHookExit lib mpl i s0 sf') := by
  rcases hret with ⟨hpc, hsp, hrun⟩
  have hpc' : sf'.pc = mpl.base i + 1#64 := by
    simpa [multiCodeROHookEntry, State.setMem, State.setPC, State.writeReg64, State.readReg64,
      Reg.lr] using hpc
  have hsp' : sf'.sp = s0.sp := by
    simpa [multiCodeROHookEntry, State.setMem, State.setPC, State.writeReg64] using hsp
  simp [Returned, multiCodeROHookExit, hpc', hrun, hsp', State.setMem, State.setPC, State.writeReg64]

theorem multiCodeROHookExit_cc {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    {i : Nat} {entry_pc : BitVec 64} {s0 sf' : State}
    (hcc : CallingConventionPreserved (multiCodeROHookEntry lib mpl i entry_pc s0) sf') :
    CallingConventionPreserved s0 (multiCodeROHookExit lib mpl i s0 sf') := by
  rcases hcc with ⟨hsp, hcs⟩
  have hsp' : sf'.sp = s0.sp := by
    simpa [multiCodeROHookEntry, State.setMem, State.setPC, State.writeReg64] using hsp
  refine ⟨?_, ?_⟩
  · unfold multiCodeROHookExit
    dsimp only
    split <;> simp [hsp', State.setMem, State.setPC, State.writeReg64]
  · simp only [CalleeSavedPreserved, multiCodeROHookEntry, State.setMem, State.setPC,
      State.writeReg64, State.readReg64] at hcs
    unfold multiCodeROHookExit
    dsimp only
    split <;> (simp only [CalleeSavedPreserved, State.setMem, State.setPC, State.writeReg64,
      State.readReg64]; exact hcs)

/-! ## Block Disjointness and `loadMultiCodeMem` / `restoreMultiCodeMem` Properties -/

theorem blockPatched_length_of_placeable {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    {k : Nat} (hpl : lib.Placeable mpl) (hk : k < lib.blocks.length) :
    (lib.blockPatched mpl k).length = lib.blocks[k].code.length := by
  unfold Obj.MultiPlacedLib.blockPatched
  rw [lib.blockLib_text_of_lt hk]
  exact Obj.CodeBlock.length_patched_of_aligned _ (hpl.blocks_ok k hk).len_aligned

private theorem toNat_bounds_of_inRegion {base a : BitVec 64} {len : Nat}
    (hnw : base.toNat + len ≤ 2 ^ 64) (hin : InRegion base len a) :
    base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + len := by
  have hlt : (a - base).toNat < len := hin
  bv_omega

theorem inRegion_blockPatched_unique {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    (hpl : lib.Placeable mpl) {i j : Nat} (hi : i < lib.blocks.length) (hj : j < lib.blocks.length)
    {a : BitVec 64}
    (hini : InRegion (mpl.base i) (lib.blockPatched mpl i).length a)
    (hinj : InRegion (mpl.base j) (lib.blockPatched mpl j).length a) :
    i = j := by
  have hleni := blockPatched_length_of_placeable hpl hi
  have hlenj := blockPatched_length_of_placeable hpl hj
  rw [hleni] at hini
  rw [hlenj] at hinj
  have hnwi : (mpl.base i).toNat + lib.blocks[i].code.length ≤ 2 ^ 64 := (hpl.blocks_ok i hi).no_wrap
  have hnwj : (mpl.base j).toNat + lib.blocks[j].code.length ≤ 2 ^ 64 := (hpl.blocks_ok j hj).no_wrap
  have ⟨hbi1, hbi2⟩ := toNat_bounds_of_inRegion hnwi hini
  have ⟨hbj1, hbj2⟩ := toNat_bounds_of_inRegion hnwj hinj
  rcases Nat.lt_trichotomy i j with hij | rfl | hji
  · rcases hpl.blocks_disjoint i j hi hj hij with hdisj | hdisj <;> omega
  · rfl
  · rcases hpl.blocks_disjoint j i hj hi hji with hdisj | hdisj <;> omega

theorem findCodeBlock_lt {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    {a : BitVec 64} {k : Nat} (h : lib.findCodeBlock mpl a = some k) :
    k < lib.blocks.length :=
  List.mem_range.mp (List.mem_of_find?_eq_some h)

theorem findCodeBlock_inRegion {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    {a : BitVec 64} {k : Nat} (h : lib.findCodeBlock mpl a = some k) :
    InRegion (mpl.base k) (lib.blockPatched mpl k).length a := by
  have hf : (List.range lib.blocks.length).find?
      (fun j => decide (InRegion (mpl.base j) (lib.blockPatched mpl j).length a)) = some k := h
  have hd := List.find?_some hf
  exact of_decide_eq_true hd

theorem findCodeBlock_eq_some_of_inRegion {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    (hpl : lib.Placeable mpl) {k : Nat} (hk : k < lib.blocks.length) {a : BitVec 64}
    (hin : InRegion (mpl.base k) (lib.blockPatched mpl k).length a) :
    lib.findCodeBlock mpl a = some k := by
  unfold Obj.MultiPlacedLib.findCodeBlock
  cases hf : (List.range lib.blocks.length).find?
      (fun j => decide (InRegion (mpl.base j) (lib.blockPatched mpl j).length a)) with
  | none =>
    have hall := List.find?_eq_none.mp hf k (List.mem_range.mpr hk)
    simp [hin] at hall
  | some j =>
    have hj : j < lib.blocks.length := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    have hd := List.find?_some hf
    have hinj : InRegion (mpl.base j) (lib.blockPatched mpl j).length a :=
      of_decide_eq_true hd
    rw [inRegion_blockPatched_unique hpl hj hk hinj hin]

theorem findCodeBlock_eq_none_iff {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    {a : BitVec 64} :
    lib.findCodeBlock mpl a = none ↔
      ∀ k, k < lib.blocks.length → ¬ InRegion (mpl.base k) (lib.blockPatched mpl k).length a := by
  unfold Obj.MultiPlacedLib.findCodeBlock
  rw [List.find?_eq_none]
  constructor
  · intro h k hk
    simpa using h k (List.mem_range.mpr hk)
  · intro h k hk
    simpa using h k (List.mem_range.mp hk)

theorem loadMultiCodeMem_cells_some {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    {m : Memory} {a : BitVec 64} {k : Nat} (h : lib.findCodeBlock mpl a = some k) :
    (loadMultiCodeMem lib mpl m).cells a =
      some (some { Perm.rx with anon := m.isAnon a },
        (lib.blockPatched mpl k)[(a - mpl.base k).toNat]'(findCodeBlock_inRegion h)) := by
  unfold loadMultiCodeMem
  dsimp only
  split
  · rename_i j hj
    have heq : j = k := Option.some.inj (hj.symm.trans h)
    subst heq
    rfl
  · rename_i hn
    rw [h] at hn
    cases hn

theorem loadMultiCodeMem_cells_none {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    {m : Memory} {a : BitVec 64} (h : lib.findCodeBlock mpl a = none) :
    (loadMultiCodeMem lib mpl m).cells a = m.cells a := by
  unfold loadMultiCodeMem
  dsimp only
  split
  · rename_i j hj
    rw [h] at hj
    cases hj
  · rfl

theorem restoreMultiCodeMem_cells_some {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    {m0 mf : Memory} {a : BitVec 64} {k : Nat} (h : lib.findCodeBlock mpl a = some k) :
    (restoreMultiCodeMem lib mpl m0 mf).cells a = m0.cells a := by
  simp [restoreMultiCodeMem, h]

theorem restoreMultiCodeMem_cells_none {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    {m0 mf : Memory} {a : BitVec 64} (h : lib.findCodeBlock mpl a = none) :
    (restoreMultiCodeMem lib mpl m0 mf).cells a = mf.cells a := by
  simp [restoreMultiCodeMem, h]

private theorem read8_eq_of_cells_eq {m1 m2 : Memory} {a : BitVec 64}
    (h : m1.cells a = m2.cells a) : m1.read8 a = m2.read8 a := by
  simp [Memory.read8, h]

private theorem perm_eq_of_cells_eq {m1 m2 : Memory} {a : BitVec 64}
    (h : m1.cells a = m2.cells a) : m1.perm a = m2.perm a := by
  simp [Memory.perm, h]

private theorem isLazyFree_eq_of_cells_eq {m1 m2 : Memory} {a : BitVec 64}
    (h : m1.cells a = m2.cells a) : m1.isLazyFree a = m2.isLazyFree a := by
  simp [Memory.isLazyFree, h]

private theorem isAnon_eq_of_cells_eq {m1 m2 : Memory} {a : BitVec 64}
    (h : m1.cells a = m2.cells a) : m1.isAnon a = m2.isAnon a := by
  simp [Memory.isAnon, h]

/-- Under `lib.Placeable mpl`, `loadMultiCodeMem lib mpl m` unconditionally satisfies
    `lib.CodeLoaded mpl` for every memory `m`. -/
theorem codeLoaded_loadMultiCodeMem {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    (hpl : lib.Placeable mpl) (m : Memory) :
    lib.CodeLoaded mpl (loadMultiCodeMem lib mpl m) := by
  intro k hk
  have hbk := hpl.blocks_ok k hk
  have hbase_al : (mpl.base k).toNat % 4 = 0 := by
    have ⟨_, ha4⟩ := hbk.align_pos
    exact Nat.dvd_trans (Nat.dvd_of_mod_eq_zero ha4) (Nat.dvd_of_mod_eq_zero hbk.base_aligned)
      |> Nat.mod_eq_zero_of_dvd
  have hlen : (lib.blockPatched mpl k).length = lib.blocks[k].code.length :=
    blockPatched_length_of_placeable hpl hk
  have hnw0 : (mpl.base k).toNat + lib.blocks[k].code.length ≤ 2 ^ 64 := hbk.no_wrap
  have hnw : (mpl.base k).toNat + (lib.blockPatched mpl k).length ≤ 2 ^ 64 := by
    omega
  refine Program.CodeLoaded.intro hbase_al hnw fun idx hidx => ?_
  have hidx' : idx < (lib.blockPatched mpl k).length := hidx
  let a := mpl.base k + BitVec.ofNat 64 idx
  have hsub : (a - mpl.base k).toNat = idx := by
    have : a - mpl.base k = BitVec.ofNat 64 idx := by
      dsimp [a]; rw [BitVec.add_comm, BitVec.add_sub_cancel]
    rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hin : InRegion (mpl.base k) (lib.blockPatched mpl k).length a := by
    simp only [InRegion, hsub]; exact hidx'
  have hf : lib.findCodeBlock mpl a = some k :=
    findCodeBlock_eq_some_of_inRegion hpl hk hin
  have hcells := loadMultiCodeMem_cells_some (m := m) hf
  change (loadMultiCodeMem lib mpl m).read8 a = (lib.blockPatched mpl k)[idx]'hidx' ∧
    (loadMultiCodeMem lib mpl m).perm a = some Perm.rx ∧
    (loadMultiCodeMem lib mpl m).isLazyFree a = false
  refine ⟨?_, ?_, ?_⟩
  · simp only [Memory.read8, hcells]
    congr 1
  · simp only [Memory.perm, Perm.rwx, Perm.rx, hcells]
  · simp only [Memory.isLazyFree, Perm.rx, hcells]

/-- Restoring caller code-block cells via `restoreMultiCodeMem` preserves frozen bytes whenever
    execution from `loadMultiCodeMem lib mpl m0` to `mf'` satisfied `KeepsFrozen`. -/
theorem keepsFrozen_restoreMultiCodeMem {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    {m0 mf' : Memory} (hkf : (loadMultiCodeMem lib mpl m0).KeepsFrozen mf') :
    m0.KeepsFrozen (restoreMultiCodeMem lib mpl m0 mf') := by
  intro a hfr
  cases hf : lib.findCodeBlock mpl a with
  | some k =>
    have hc := restoreMultiCodeMem_cells_some (m0 := m0) (mf := mf') hf
    exact ⟨read8_eq_of_cells_eq hc, perm_eq_of_cells_eq hc,
      isLazyFree_eq_of_cells_eq hc, isAnon_eq_of_cells_eq hc⟩
  | none =>
    have hc0 := loadMultiCodeMem_cells_none (m := m0) hf
    have hcf := restoreMultiCodeMem_cells_none (m0 := m0) (mf := mf') hf
    have hfr' : ((loadMultiCodeMem lib mpl m0).perm a).frozen = true := by
      rwa [perm_eq_of_cells_eq hc0]
    obtain ⟨hr, hp, hlf, han⟩ := hkf a hfr'
    rw [read8_eq_of_cells_eq hc0] at hr
    rw [perm_eq_of_cells_eq hc0] at hp
    rw [isLazyFree_eq_of_cells_eq hc0] at hlf
    rw [isAnon_eq_of_cells_eq hc0] at han
    exact ⟨(read8_eq_of_cells_eq hcf).trans hr, (perm_eq_of_cells_eq hcf).trans hp,
      (isLazyFree_eq_of_cells_eq hcf).trans hlf, (isAnon_eq_of_cells_eq hcf).trans han⟩

/-! ## `lib.codeRO mpl` Heap Characterization and Overlay/Restore Framing -/

private theorem read8_of_readBytes_inRegion {m : Memory} {base : BitVec 64} {bs : List (BitVec 8)}
    (hread : m.readBytes base bs.length = bs)
    {a : BitVec 64} (hin : InRegion base bs.length a) :
    m.read8 a = bs[(a - base).toNat]'hin := by
  have hk : (a - base).toNat < bs.length := hin
  have ha : base + BitVec.ofNat 64 (a - base).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  have hget : ∀ (m' : Memory) (b' : BitVec 64) (xs : List (BitVec 8)) (k : Nat) (hlt : k < xs.length),
      m'.readBytes b' xs.length = xs → m'.read8 (b' + BitVec.ofNat 64 k) = xs[k]'hlt := by
    intro m' b' xs
    induction xs generalizing b' with
    | nil => intro k hlt; cases hlt
    | cons x rest ih =>
      intro k hlt hrb
      simp only [List.length_cons, Memory.readBytes_succ, List.cons.injEq] at hrb
      cases k with
      | zero => simpa using hrb.1
      | succ k' =>
        have hk' : k' < rest.length := by simp at hlt; omega
        have hadd : b' + BitVec.ofNat 64 (k' + 1) = (b' + 1#64) + BitVec.ofNat 64 k' := by bv_arith
        rw [hadd]
        exact ih (b' + 1#64) k' hk' hrb.2
  have h1 := hget m base bs (a - base).toNat hk hread
  rwa [ha] at h1

private theorem blockCodeRO_holds_phys {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    (hpl : lib.Placeable mpl) {k : Nat} (hk : k < lib.blocks.length) {h : Heap}
    (hh : (lib.blockCodeRO mpl k).holds h) :
    (∀ a (hin : InRegion (mpl.base k) (lib.blockPatched mpl k).length a),
      h.phys a = some (.ro ((lib.blockPatched mpl k)[(a - mpl.base k).toNat]'hin))) ∧
    (∀ a, ¬ InRegion (mpl.base k) (lib.blockPatched mpl k).length a → h.phys a = none) := by
  have hlen := blockPatched_length_of_placeable hpl hk
  have hnw0 : (mpl.base k).toNat + lib.blocks[k].code.length ≤ 2 ^ 64 := (hpl.blocks_ok k hk).no_wrap
  have hblk := IsBlockRO.pointsToBytesRO (mpl.base k) (lib.blockPatched mpl k) (by omega)
  obtain ⟨m_w, hread, rfl⟩ := (hblk.iff h).mp hh
  refine ⟨fun a hin => ?_, fun a hnin => ?_⟩
  · simp only [regionHeapRO, hin, ↓reduceIte]
    rw [read8_of_readBytes_inRegion hread hin]
  · simp [regionHeapRO, hnin]

private theorem sepAll_blockCodeRO_holds_phys {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    (hpl : lib.Placeable mpl) :
    ∀ (ks : List Nat) (_ : ∀ k ∈ ks, k < lib.blocks.length) {h : Heap},
      (Obj.sepAll (ks.map (lib.blockCodeRO mpl))).holds h →
      (∀ k ∈ ks, ∀ a (hin : InRegion (mpl.base k) (lib.blockPatched mpl k).length a),
        h.phys a = some (.ro ((lib.blockPatched mpl k)[(a - mpl.base k).toNat]'hin))) ∧
      (∀ a, (∀ k ∈ ks, ¬ InRegion (mpl.base k) (lib.blockPatched mpl k).length a) →
        h.phys a = none)
  | [], _, h, hh => by
    rw [List.map_nil, Obj.sepAll_nil] at hh
    simp only [SepProp.holds_emp_iff] at hh
    subst hh
    exact ⟨(fun _ hm => nomatch hm), fun _ _ => by simp [Heap.empty]⟩
  | k :: rest, hks, h, hh => by
    rw [List.map_cons, Obj.sepAll_cons] at hh
    simp only [SepProp.holds_sepConj_iff] at hh
    rcases hh with ⟨h1, h2, _, rfl, hh1, hh2⟩
    have hk : k < lib.blocks.length := hks k (by simp)
    have hrest : ∀ j ∈ rest, j < lib.blocks.length := fun j hj => hks j (by simp [hj])
    obtain ⟨h1_in, h1_out⟩ := blockCodeRO_holds_phys hpl hk hh1
    obtain ⟨h2_in, h2_out⟩ := sepAll_blockCodeRO_holds_phys hpl rest hrest hh2
    refine ⟨fun j hj a hin => ?_, fun a hall => ?_⟩
    · simp only [Heap.union]
      rcases List.mem_cons.mp hj with rfl | hj_rest
      · rw [h1_in a hin]
      · have hj_lt : j < lib.blocks.length := hrest j hj_rest
        by_cases hink : InRegion (mpl.base k) (lib.blockPatched mpl k).length a
        · have heq := inRegion_blockPatched_unique hpl hk hj_lt hink hin
          subst heq
          rw [h1_in a hink]
        · rw [h1_out a hink]
          exact h2_in j hj_rest a hin
    · simp only [Heap.union]
      rw [h1_out a (hall k (by simp)), h2_out a (fun j hj => hall j (by simp [hj]))]

theorem codeRO_holds_phys_some {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    (hpl : lib.Placeable mpl) {h : Heap} (hh : (lib.codeRO mpl).holds h)
    {a : BitVec 64} {k : Nat} (hf : lib.findCodeBlock mpl a = some k) :
    h.phys a = some (.ro ((lib.blockPatched mpl k)[(a - mpl.base k).toNat]'(findCodeBlock_inRegion hf))) := by
  have hk : k ∈ List.range lib.blocks.length := List.mem_range.mpr (findCodeBlock_lt hf)
  have ⟨hin_all, _⟩ := sepAll_blockCodeRO_holds_phys hpl (List.range lib.blocks.length)
    (fun j hj => List.mem_range.mp hj) hh
  exact hin_all k hk a (findCodeBlock_inRegion hf)

private theorem option_perm_mapped_of_r {p : Option Perm} (hr : p.r = true) :
    p.mapped = true := by
  cases p <;> simp at hr ⊢

/-- Under `lib.Placeable mpl`, overlaying `lib`'s code blocks via `loadMultiCodeMem` preserves
    satisfaction of `lib.codeRO mpl ∗ P` for every `P : SepProp`, without `SepProp.NoRO` or
    `PermsRX`. -/
theorem satisfies_loadMultiCodeMem {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    {m0 : Memory} {P : SepProp}
    (hpl : lib.Placeable mpl) (hsat : m0 ⊨ lib.codeRO mpl ∗ P) :
    loadMultiCodeMem lib mpl m0 ⊨ lib.codeRO mpl ∗ P := by
  simp only [SepProp.satisfies_iff, SepProp.holds_sepConj_iff] at hsat ⊢
  rcases hsat with ⟨_, ⟨h_code, h_rest, hd, rfl, hcode, hP⟩, hm0⟩
  refine ⟨h_code.union h_rest, ⟨h_code, h_rest, hd, rfl, hcode, hP⟩, ?_⟩
  simp only [Heap.Matches] at hm0 ⊢
  rcases hm0 with ⟨hm0_phys, hm0_gv, hm0_map⟩
  refine ⟨fun a c hac => ?_, hm0_gv, fun a hmap => ?_⟩
  · cases hf : lib.findCodeBlock mpl a with
    | some k =>
      have hc_code := codeRO_holds_phys_some hpl hcode hf
      have hc_union : (h_code.union h_rest).phys a =
          some (.ro ((lib.blockPatched mpl k)[(a - mpl.base k).toNat]'(findCodeBlock_inRegion hf))) := by
        simp [Heap.union, hc_code]
      rw [hc_union] at hac
      injection hac with hc_eq
      subst hc_eq
      have hcells := loadMultiCodeMem_cells_some (m := m0) hf
      simp [Memory.read8, Memory.perm, Memory.isLazyFree, Perm.rwx, Perm.rx, hcells]
    | none =>
      have hcells := loadMultiCodeMem_cells_none (m := m0) hf
      have hm := hm0_phys a c hac
      cases c <;>
        simpa only [read8_eq_of_cells_eq hcells, perm_eq_of_cells_eq hcells,
          isLazyFree_eq_of_cells_eq hcells] using hm
  · cases hf : lib.findCodeBlock mpl a with
    | some k =>
      have hcells := loadMultiCodeMem_cells_some (m := m0) hf
      refine ⟨by simp [Memory.perm, Perm.rwx, Perm.rx, hcells], ?_⟩
      have han_eq : (loadMultiCodeMem lib mpl m0).isAnon a = m0.isAnon a := by
        simp [Memory.isAnon, hcells]
      exact han_eq.trans (hm0_map a hmap).2
    | none =>
      have hcells := loadMultiCodeMem_cells_none (m := m0) hf
      rw [perm_eq_of_cells_eq hcells, isAnon_eq_of_cells_eq hcells]
      exact hm0_map a hmap

/-- Under `lib.Placeable mpl`, restoring `m0`'s cells across `lib`'s code blocks via
    `restoreMultiCodeMem` preserves satisfaction of `lib.codeRO mpl ∗ Q` whenever execution from
    `loadMultiCodeMem lib mpl m0` to `mf'` satisfied `KeepsFrozen`, `m0` initially satisfied
    `lib.codeRO mpl ∗ R₀`, and `mf'` satisfies `lib.codeRO mpl ∗ Q`. -/
theorem satisfies_restoreMultiCodeMem {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement}
    {m0 mf' : Memory} {R₀ Q : SepProp}
    (hpl : lib.Placeable mpl)
    (hkf : (loadMultiCodeMem lib mpl m0).KeepsFrozen mf')
    (hsat0 : m0 ⊨ lib.codeRO mpl ∗ R₀)
    (hsatf : mf' ⊨ lib.codeRO mpl ∗ Q) :
    restoreMultiCodeMem lib mpl m0 mf' ⊨ lib.codeRO mpl ∗ Q := by
  simp only [SepProp.satisfies_iff, SepProp.holds_sepConj_iff] at hsat0 hsatf ⊢
  rcases hsat0 with ⟨_, ⟨h_code0, h_r0, _, rfl, hcode0, _⟩, hm0⟩
  rcases hsatf with ⟨_, ⟨h_codef, h_q, hdf, rfl, hcodef, hQ⟩, hmf⟩
  simp only [Heap.Matches] at hm0 hmf ⊢
  rcases hm0 with ⟨hm0_phys, _, _⟩
  rcases hmf with ⟨hmf_phys, hmf_gv, hmf_map⟩
  refine ⟨h_codef.union h_q, ⟨h_codef, h_q, hdf, rfl, hcodef, hQ⟩,
    ⟨fun a c hac => ?_, hmf_gv, fun a hmap => ?_⟩⟩
  · cases hf : lib.findCodeBlock mpl a with
    | some k =>
      have hc0 := codeRO_holds_phys_some hpl hcode0 hf
      have hc0_u : (h_code0.union h_r0).phys a =
          some (.ro ((lib.blockPatched mpl k)[(a - mpl.base k).toNat]'(findCodeBlock_inRegion hf))) := by
        simp [Heap.union, hc0]
      have hm0_at := hm0_phys a _ hc0_u
      have hcf := codeRO_holds_phys_some hpl hcodef hf
      have hcf_u : (h_codef.union h_q).phys a =
          some (.ro ((lib.blockPatched mpl k)[(a - mpl.base k).toNat]'(findCodeBlock_inRegion hf))) := by
        simp [Heap.union, hcf]
      rw [hcf_u] at hac
      injection hac with hc_eq
      subst hc_eq
      have hcells := restoreMultiCodeMem_cells_some (m0 := m0) (mf := mf') hf
      rw [read8_eq_of_cells_eq hcells, perm_eq_of_cells_eq hcells, isLazyFree_eq_of_cells_eq hcells]
      exact hm0_at
    | none =>
      have hcells := restoreMultiCodeMem_cells_none (m0 := m0) (mf := mf') hf
      have hm := hmf_phys a c hac
      cases c <;>
        simpa only [read8_eq_of_cells_eq hcells, perm_eq_of_cells_eq hcells,
          isLazyFree_eq_of_cells_eq hcells] using hm
  · cases hf : lib.findCodeBlock mpl a with
    | some k =>
      have hc0 := codeRO_holds_phys_some hpl hcode0 hf
      have hc0_u : (h_code0.union h_r0).phys a =
          some (.ro ((lib.blockPatched mpl k)[(a - mpl.base k).toNat]'(findCodeBlock_inRegion hf))) := by
        simp [Heap.union, hc0]
      have hm0_at := hm0_phys a _ hc0_u
      have hcells := restoreMultiCodeMem_cells_some (m0 := m0) (mf := mf') hf
      have hcl := loadMultiCodeMem_cells_some (m := m0) hf
      have hfr_load : ((loadMultiCodeMem lib mpl m0).perm a).frozen = true := by
        simp [Memory.perm, Perm.rwx, Perm.rx, Perm.frozen, hcl]
      have ⟨_, _, _, han_kf⟩ := hkf a hfr_load
      have han_load : (loadMultiCodeMem lib mpl m0).isAnon a = m0.isAnon a := by
        simp [Memory.isAnon, hcl]
      refine ⟨?_, ?_⟩
      · rw [perm_eq_of_cells_eq hcells]
        exact option_perm_mapped_of_r hm0_at.2.1
      · rw [isAnon_eq_of_cells_eq hcells, ← han_load, ← han_kf]
        exact (hmf_map a hmap).2
    | none =>
      have hcells := restoreMultiCodeMem_cells_none (m0 := m0) (mf := mf') hf
      rw [perm_eq_of_cells_eq hcells, isAnon_eq_of_cells_eq hcells]
      exact hmf_map a hmap

/-! ## Deterministic `codeROSubroutineHook` Evaluation and `HookOk` Lifting -/

private theorem fetchMem_sentinel_lr {prog : Program} (m : Memory)
    (h_al : prog.base.toNat % 4 = 0) :
    prog.fetchMem m (prog.base + 1#64) = none := by
  have h1 : (prog.base + 1#64).toNat % 4 ≠ 0 := by
    bv_omega
  simp only [Program.fetchMem, h1, ne_eq, not_false_eq_true, ↓reduceIte, ite_self]

open Classical in
theorem codeROSubroutineHook_eq_of_steps_outcome {α : Type}
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {fnName : String}
    {externs overrides : String → Option (State → State)} {svc : State → State}
    {i off : Nat} {spec : Spec α} {x : α} {R' : SepProp} {s0 sf' : State}
    (hlook : Obj.lookupBlockSym fnName lib.blocks = some (i, off))
    (h_al : (mpl.base i).toNat % 4 = 0)
    (h_ext1 : (lib.blockProgram mpl i externs overrides svc).externAt? (mpl.base i + 1#64) = none)
    (h_steps : Steps (lib.blockProgram mpl i externs overrides svc)
      (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) sf')
    (hout : SubroutineOutcome spec x R'
      (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) sf') :
    lib.codeROSubroutineHook mpl fnName externs overrides svc s0 =
      multiCodeROHookExit lib mpl i s0 sf' := by
  let prog := lib.blockProgram mpl i externs overrides svc
  let s0' := multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0
  have hbase : prog.base = mpl.base i := rfl
  have hlr : s0'.readReg64 Reg.lr = prog.base + 1#64 := rfl
  have h_until : StepsUntil prog (SubroutineStop s0') s0' sf' :=
    stepsUntil_of_steps_subroutineOutcome_sentinel_lr
      (fun m => hlr ▸ fetchMem_sentinel_lr m (hbase ▸ h_al))
      (hlr ▸ hbase ▸ h_ext1) h_steps hout
  have hex : ∃ sf, StepsUntil prog (SubroutineStop s0') s0' sf ∧ SubroutineStop s0' sf :=
    ⟨sf', h_until, hout.to_subroutineStop⟩
  simp only [Obj.MultiPlacedLib.codeROSubroutineHook, hlook]
  change (if h : ∃ sf, StepsUntil prog (SubroutineStop s0') s0' sf ∧ SubroutineStop s0' sf then
      multiCodeROHookExit lib mpl i s0 (Classical.choose h) else s0) =
    multiCodeROHookExit lib mpl i s0 sf'
  simp only [hex, ↓reduceDIte]
  congr 1
  exact StepsUntil.deterministic (Classical.choose_spec hex).1 (Classical.choose_spec hex).2
    h_until hout.to_subroutineStop

/-- Lifts `subroutine_ok` for `Obj.MultiPlacedLib.codeROSubroutineHook` at a `Placeable` placement
    `mpl` and supervisor-call handler `svc` to `HookOk` using `lib.codeRO mpl` (`↦ᵣ`) in `spec.pre`
    (without `PermsRX`, `CodeLoaded s0.mem`, or `SepProp.NoRO`), supporting existential inner ghost
    parameters `y : β` and an internal call frame `Q` preserved across `.Running` and dropped when
    `spec.onOom` requires only `inner.onOom`. -/
theorem subroutineHook_ok_of_multiCodeRO_at {α β : Type}
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {fnName : String}
    {externs overrides : String → Option (State → State)} {svc : State → State}
    {i off : Nat} {inner : Spec β} {spec : Spec α}
    (Q : α → β → State → SepProp := fun _ _ _ => emp)
    (φ : α → β → State → Prop := fun _ _ _ => True)
    (h_pl : lib.Placeable mpl)
    (h_look : Obj.lookupBlockSym fnName lib.blocks = some (i, off))
    (h_sub : subroutine_ok (lib.blockProgram mpl i externs overrides svc)
      (lib.fnAddr mpl fnName) (lib.withCodeLoaded mpl inner))
    (h_pre : ∀ x s0,
      spec.pre x s0 ⊢
        ∃∗ y : β,
          ⌜φ x y s0⌝ ∗
            lib.codeRO mpl ∗
            inner.pre y (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) ∗
            Q x y s0)
    (h_post : ∀ x y s0 sf',
      φ x y s0 →
      lib.CodeLoaded mpl sf'.mem →
      Returned (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) sf' →
      CallingConventionPreserved (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) sf' →
      (lib.codeRO mpl ∗
        inner.post y (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) sf' ∗
        Q x y s0) ⊢
        spec.post x s0 (multiCodeROHookExit lib mpl i s0 sf'))
    (h_ext1 :
        externs = (fun _ => none) ∨
        0 < (lib.blockLib i).text.code.length ∨
        (lib.blockProgram mpl i externs overrides svc).externAt? (mpl.base i + 1#64) = none := by
      first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl (by decide)))
    (h_no_panic : ∀ y R' s0 sf', sf'.status = .Panicked →
      ¬(sf'.mem ⊨
        inner.onPanic y (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) sf' ∗ R') := by
      intro _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ y code R' s0 sf', sf'.status = .Exited code →
      ¬(sf'.mem ⊨
        inner.onExit y code (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) sf' ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ x y s0 sf',
      φ x y s0 →
      lib.CodeLoaded mpl sf'.mem →
      sf'.status = .OutOfMemory →
      (inner.onOom y (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) sf' ⊢
        spec.onOom x s0 (multiCodeROHookExit lib mpl i s0 sf')) ∨
      ((lib.codeRO mpl ∗
        inner.onOom y (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) sf' ∗
        Q x y s0) ⊢
        spec.onOom x s0 (multiCodeROHookExit lib mpl i s0 sf')) := by
      intro _ _ _ sf' _ _ _
      left
      try simp only [Spec.codeROMultiSubroutineHook,
        Obj.MultiPlacedLib.codeROSubroutineHookSpec, Spec.allowOom]
      first
      | exact Entails.refl _
      | exact Entails.sepExists_right sf' (Entails.pure_right rfl (Entails.refl _))
      | exact Entails.pure_left_only fun _ => Entails.pure_right_only trivial (Entails.refl _)
      | exact Entails.pure_left fun _ => Entails.pure_right trivial (Entails.refl _)
      | exact Entails.pure_left_only fun h => False.elim h) :
    HookOk (lib.codeROSubroutineHook mpl fnName externs overrides svc) spec := by
  have hi : i < lib.blocks.length := lookupBlockSym_lt h_look
  let prog := lib.blockProgram mpl i externs overrides svc
  intro x R s0 hrun hpre_sat hsp
  have hpre_ex : s0.mem ⊨
      (∃∗ y : β,
        ⌜φ x y s0⌝ ∗
          lib.codeRO mpl ∗
          inner.pre y (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) ∗
          Q x y s0) ∗ R :=
    Satisfies.mono (sepConj_mono_left (h_pre x s0)) hpre_sat
  have ⟨y, hφ, hy_sat⟩ : ∃ y : β, φ x y s0 ∧ s0.mem ⊨
      (lib.codeRO mpl ∗
        inner.pre y (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) ∗
        Q x y s0) ∗ R := by
    have ⟨y, hy0⟩ : ∃ y : β, s0.mem ⊨
        (⌜φ x y s0⌝ ∗
          lib.codeRO mpl ∗
          inner.pre y (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0) ∗
          Q x y s0) ∗ R := by
      simp only [SepProp.satisfies_iff, SepProp.holds_sepConj_iff, SepProp.holds_sepExists_iff] at hpre_ex ⊢
      rcases hpre_ex with ⟨h, ⟨h1, h2, hdisj, rfl, ⟨y, hy1⟩, h2_holds⟩, hm⟩
      exact ⟨y, h1.union h2, ⟨h1, h2, hdisj, rfl, hy1, h2_holds⟩, hm⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hy0
    exact ⟨y, hy0.1, by simpa only [sepConj_assoc] using hy0.2⟩
  let s0' := multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0
  have hy_sat0 : s0.mem ⊨ lib.codeRO mpl ∗ (inner.pre y s0' ∗ (Q x y s0 ∗ R)) := by
    simpa only [s0', sepConj_assoc] using hy_sat
  have hs0'_sat : s0'.mem ⊨ lib.codeRO mpl ∗ (inner.pre y s0' ∗ (Q x y s0 ∗ R)) :=
    satisfies_loadMultiCodeMem h_pl hy_sat0
  have hL0' : lib.CodeLoaded mpl s0'.mem := codeLoaded_loadMultiCodeMem h_pl s0.mem
  have hp0' : prog.CodeLoaded s0'.mem := hL0'.blockProgram hi
  let R' := lib.codeRO mpl ∗ Q x y s0 ∗ R
  have hs0'_pre : s0'.mem ⊨ (lib.withCodeLoaded mpl inner).pre y s0' ∗ R' := by
    dsimp only [Obj.MultiPlacedLib.withCodeLoaded, R']
    rw [sepConj_comm (inner.pre y s0'), sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hL0', ?_⟩
    have hcomm : lib.codeRO mpl ∗ inner.pre y s0' ∗ Q x y s0 ∗ R =
        inner.pre y s0' ∗ lib.codeRO mpl ∗ Q x y s0 ∗ R := by
      rw [← sepConj_assoc (lib.codeRO mpl) (inner.pre y s0'),
          sepConj_comm (lib.codeRO mpl) (inner.pre y s0'),
          sepConj_assoc]
    simpa only [sepConj_assoc, ← hcomm] using hs0'_sat
  obtain ⟨sf', h_steps, hout⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 h_sub y R' s0' rfl hrun hs0'_pre hsp) hp0'
  have hLf : lib.CodeLoaded mpl sf'.mem := hL0'.of_keepsFrozen h_steps.keepsFrozen
  have hext1 : prog.externAt? (mpl.base i + 1#64) = none := by
    rcases h_ext1 with rfl | hpos | hext
    · exact lib.externAt?_base_add_one_noExterns h_pl hi
    · rw [lib.blockLib_text_of_lt hi] at hpos
      exact lib.externAt?_base_add_one_of_pos h_pl hi hpos
    · exact hext
  have hhook_eq : lib.codeROSubroutineHook mpl fnName externs overrides svc s0 =
      multiCodeROHookExit lib mpl i s0 sf' :=
    codeROSubroutineHook_eq_of_steps_outcome h_look hp0'.aligned hext1 h_steps hout
  rw [hhook_eq]
  have hkf : s0.mem.KeepsFrozen (multiCodeROHookExit lib mpl i s0 sf').mem :=
    keepsFrozen_restoreMultiCodeMem h_steps.keepsFrozen
  have hsym : (multiCodeROHookExit lib mpl i s0 sf').symtab = s0.symtab := by
    rw [multiCodeROHookExit_symtab, h_steps.symtab_eq, multiCodeROHookEntry_symtab]
  rcases hout with ⟨hret, hcc, hpost_sat⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine ⟨hkf, hsym, Or.inl ⟨multiCodeROHookExit_returned hret, multiCodeROHookExit_cc hcc, ?_⟩⟩
    dsimp only [Obj.MultiPlacedLib.withCodeLoaded, R'] at hpost_sat
    have hsf'_reord : sf'.mem ⊨ lib.codeRO mpl ∗ ((inner.post y s0' sf' ∗ Q x y s0) ∗ R) := by
      have heq : inner.post y s0' sf' ∗ lib.codeRO mpl ∗ Q x y s0 ∗ R =
          lib.codeRO mpl ∗ ((inner.post y s0' sf' ∗ Q x y s0) ∗ R) := by
        rw [← sepConj_assoc (inner.post y s0' sf') (lib.codeRO mpl),
            sepConj_comm (inner.post y s0' sf') (lib.codeRO mpl),
            sepConj_assoc, sepConj_assoc]
      rwa [← heq]
    have hsf_restored :
        (multiCodeROHookExit lib mpl i s0 sf').mem ⊨
          (lib.codeRO mpl ∗ inner.post y s0' sf' ∗ Q x y s0) ∗ R := by
      simpa only [multiCodeROHookExit_mem, sepConj_assoc] using
        satisfies_restoreMultiCodeMem h_pl h_steps.keepsFrozen hy_sat0 hsf'_reord
    exact Satisfies.mono (sepConj_mono_left (h_post x y s0 sf' hφ hLf hret hcc)) hsf_restored
  · exact False.elim (h_no_panic y R' s0 sf' hpan hq)
  · exact False.elim (h_no_exit y code R' s0 sf' hex hq)
  · refine ⟨hkf, hsym, Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))⟩
    · simp [hoom]
    · dsimp only [Obj.MultiPlacedLib.withCodeLoaded, R'] at hq
      have hsf'_reord : sf'.mem ⊨ lib.codeRO mpl ∗ (Q x y s0 ∗ (inner.onOom y s0' sf' ∗ R)) := by
        have heq : inner.onOom y s0' sf' ∗ lib.codeRO mpl ∗ Q x y s0 ∗ R =
            lib.codeRO mpl ∗ (Q x y s0 ∗ (inner.onOom y s0' sf' ∗ R)) := by
          rw [← sepConj_assoc (inner.onOom y s0' sf') (lib.codeRO mpl),
              sepConj_comm (inner.onOom y s0' sf') (lib.codeRO mpl),
              sepConj_assoc,
              ← sepConj_assoc (inner.onOom y s0' sf') (Q x y s0),
              sepConj_comm (inner.onOom y s0' sf') (Q x y s0),
              sepConj_assoc]
        rwa [← heq]
      have hsf_restored :
          (multiCodeROHookExit lib mpl i s0 sf').mem ⊨
            lib.codeRO mpl ∗ (Q x y s0 ∗ (inner.onOom y s0' sf' ∗ R)) := by
        simpa only [multiCodeROHookExit_mem] using
          satisfies_restoreMultiCodeMem h_pl h_steps.keepsFrozen hy_sat0 hsf'_reord
      rcases h_oom x y s0 sf' hφ hLf hoom with h_oom_drop | h_oom_keep
      · have h_inner_R : (multiCodeROHookExit lib mpl i s0 sf').mem ⊨ inner.onOom y s0' sf' ∗ R :=
          Satisfies.of_sep_right (Satisfies.of_sep_right hsf_restored)
        exact Satisfies.mono (sepConj_mono_left h_oom_drop) h_inner_R
      · have h_full_R :
            (multiCodeROHookExit lib mpl i s0 sf').mem ⊨
              (lib.codeRO mpl ∗ inner.onOom y s0' sf' ∗ Q x y s0) ∗ R := by
          have heq : lib.codeRO mpl ∗ (Q x y s0 ∗ (inner.onOom y s0' sf' ∗ R)) =
              (lib.codeRO mpl ∗ inner.onOom y s0' sf' ∗ Q x y s0) ∗ R := by
            rw [sepConj_assoc (lib.codeRO mpl) (inner.onOom y s0' sf' ∗ Q x y s0) R,
                ← sepConj_assoc (Q x y s0) (inner.onOom y s0' sf') R,
                sepConj_comm (Q x y s0) (inner.onOom y s0' sf')]
          rwa [← heq]
        exact Satisfies.mono (sepConj_mono_left h_oom_keep) h_full_R

/-- Placement-quantified `lib.subroutineOk` version of `subroutineHook_ok_of_multiCodeRO_at` with
    existential inner ghost parameter `y : β`, pure side condition `φ`, and internal call frame `Q`. -/
theorem subroutineHook_ok_of_multiCodeRO_framed {S α β : Type} [ToBaseSpec S β]
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {fnName : String}
    {innerSpec : Obj.MultiPlacement → S} {spec : Spec α}
    {externs overrides : String → Option (State → State)}
    (Q : α → β → State → SepProp := fun _ _ _ => emp)
    (φ : α → β → State → Prop := fun _ _ _ => True)
    (h_pl : lib.Placeable mpl)
    (h_sub : lib.subroutineOk fnName innerSpec externs overrides)
    (h_pre : ∀ x s0,
      spec.pre x s0 ⊢
        ∃∗ y : β,
          ⌜φ x y s0⌝ ∗
            lib.codeRO mpl ∗
            (ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).pre y
              (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) ∗
            Q x y s0)
    (h_post : ∀ x y s0 sf',
      φ x y s0 →
      lib.CodeLoaded mpl sf'.mem →
      Returned (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf' →
      CallingConventionPreserved
        (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf' →
      (lib.codeRO mpl ∗
        (ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).post y
          (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf' ∗
        Q x y s0) ⊢
        spec.post x s0 (multiCodeROHookExit lib mpl (lib.fnBlockIdx fnName) s0 sf'))
    (h_ext1 :
        externs = (fun _ => none) ∨
        0 < (lib.blockLib (lib.fnBlockIdx fnName)).text.code.length ∨
        (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides).externAt?
          (mpl.base (lib.fnBlockIdx fnName) + 1#64) = none := by
      first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl (by decide)))
    (h_no_panic : ∀ y R' s0 sf', sf'.status = .Panicked →
      ¬(sf'.mem ⊨
        (ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).onPanic y
          (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf' ∗ R') := by
      intro _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ y code R' s0 sf', sf'.status = .Exited code →
      ¬(sf'.mem ⊨
        (ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).onExit y code
          (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf' ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ x y s0 sf',
      φ x y s0 →
      lib.CodeLoaded mpl sf'.mem →
      sf'.status = .OutOfMemory →
      ((ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).onOom y
        (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf' ⊢
        spec.onOom x s0 (multiCodeROHookExit lib mpl (lib.fnBlockIdx fnName) s0 sf')) ∨
      ((lib.codeRO mpl ∗
        (ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).onOom y
          (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf' ∗
        Q x y s0) ⊢
        spec.onOom x s0 (multiCodeROHookExit lib mpl (lib.fnBlockIdx fnName) s0 sf')) := by
      intro _ _ _ sf' _ _ _
      left
      try simp only [Spec.codeROMultiSubroutineHook,
        Obj.MultiPlacedLib.codeROSubroutineHookSpec, Spec.allowOom]
      first
      | exact Entails.refl _
      | exact Entails.sepExists_right sf' (Entails.pure_right rfl (Entails.refl _))
      | exact Entails.pure_left_only fun _ => Entails.pure_right_only trivial (Entails.refl _)
      | exact Entails.pure_left fun _ => Entails.pure_right trivial (Entails.refl _)
      | exact Entails.pure_left_only fun h => False.elim h) :
    HookOk (lib.codeROSubroutineHook mpl fnName externs overrides) spec := by
  obtain ⟨_, idx, off, hlook, hall⟩ := h_sub
  have hidx : lib.fnBlockIdx fnName = idx := lib.fnBlockIdx_eq_of_lookup hlook
  cases hidx
  exact subroutineHook_ok_of_multiCodeRO_at Q φ h_pl hlook (hall mpl h_pl)
    h_pre h_post h_ext1 h_no_panic h_no_exit h_oom

/-- Lift `lib.subroutineOk fnName innerSpec externs overrides` at a `Placeable` placement `mpl` to
    `HookOk (lib.codeROSubroutineHook mpl fnName externs overrides) spec` when `spec.pre` supplies
    `lib.codeRO mpl` (`↦ᵣ`), with no `PermsRX`, `CodeLoaded s0.mem`, or `SepProp.NoRO`. -/
theorem subroutineHook_ok_of_multiCodeRO {S β : Type} [ToBaseSpec S β]
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {fnName : String}
    {innerSpec : Obj.MultiPlacement → S} {spec : Spec β}
    {externs overrides : String → Option (State → State)}
    (h_pl : lib.Placeable mpl)
    (h_sub : lib.subroutineOk fnName innerSpec externs overrides)
    (h_pre : ∀ x s0,
      spec.pre x s0 ⊢
        lib.codeRO mpl ∗
          (ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).pre x
            (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0))
    (h_post : ∀ x s0 sf',
      lib.CodeLoaded mpl sf'.mem →
      Returned (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf' →
      CallingConventionPreserved
        (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf' →
      (lib.codeRO mpl ∗
        (ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).post x
          (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf') ⊢
        spec.post x s0 (multiCodeROHookExit lib mpl (lib.fnBlockIdx fnName) s0 sf'))
    (h_ext1 :
        externs = (fun _ => none) ∨
        0 < (lib.blockLib (lib.fnBlockIdx fnName)).text.code.length ∨
        (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides).externAt?
          (mpl.base (lib.fnBlockIdx fnName) + 1#64) = none := by
      first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl (by decide)))
    (h_no_panic : ∀ y R' s0 sf', sf'.status = .Panicked →
      ¬(sf'.mem ⊨
        (ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).onPanic y
          (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf' ∗ R') := by
      intro _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ y code R' s0 sf', sf'.status = .Exited code →
      ¬(sf'.mem ⊨
        (ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).onExit y code
          (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf' ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ x s0 sf',
      lib.CodeLoaded mpl sf'.mem →
      sf'.status = .OutOfMemory →
      ((ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).onOom x
        (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf' ⊢
        spec.onOom x s0 (multiCodeROHookExit lib mpl (lib.fnBlockIdx fnName) s0 sf')) ∨
      ((lib.codeRO mpl ∗
        (ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).onOom x
          (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf') ⊢
        spec.onOom x s0 (multiCodeROHookExit lib mpl (lib.fnBlockIdx fnName) s0 sf')) := by
      intro _ _ sf' _ _
      left
      try simp only [Spec.codeROMultiSubroutineHook,
        Obj.MultiPlacedLib.codeROSubroutineHookSpec, Spec.allowOom]
      first
      | exact Entails.refl _
      | exact Entails.sepExists_right sf' (Entails.pure_right rfl (Entails.refl _))
      | exact Entails.pure_left_only fun _ => Entails.pure_right_only trivial (Entails.refl _)
      | exact Entails.pure_left fun _ => Entails.pure_right trivial (Entails.refl _)
      | exact Entails.pure_left_only fun h => False.elim h) :
    HookOk (lib.codeROSubroutineHook mpl fnName externs overrides) spec := by
  refine subroutineHook_ok_of_multiCodeRO_framed (fun _ _ _ => emp) (fun x y _ => y = x) h_pl h_sub
    (fun x s0 => ?_)
    (fun x y s0 sf' hyx hLf hret hcc => ?_)
    h_ext1 h_no_panic h_no_exit
    (fun x y s0 sf' hyx hLf hoom => ?_)
  · refine Entails.trans (h_pre x s0) (Entails.sepExists_right x (Entails.pure_right rfl ?_))
    simp only [sepConj_emp]
    exact Entails.refl _
  · subst y
    simp only [sepConj_emp]
    exact h_post x s0 sf' hLf hret hcc
  · subst y
    rcases h_oom x s0 sf' hLf hoom with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (by simpa only [sepConj_emp] using h2)

/-- Direct corollary of `subroutineHook_ok_of_multiCodeRO` for `Spec.codeROMultiSubroutineHook`. -/
theorem subroutineHook_ok_codeROMultiSubroutineHook {S β : Type} [ToBaseSpec S β]
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {fnName : String}
    {spec : Obj.MultiPlacement → S}
    {externs overrides : String → Option (State → State)}
    (h_pl : lib.Placeable mpl)
    (h_sub : lib.subroutineOk fnName spec externs overrides)
    (h_ext1 :
        externs = (fun _ => none) ∨
        0 < (lib.blockLib (lib.fnBlockIdx fnName)).text.code.length ∨
        (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides).externAt?
          (mpl.base (lib.fnBlockIdx fnName) + 1#64) = none := by
      first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl (by decide)))
    (h_no_panic : ∀ y R' s0 sf', sf'.status = .Panicked →
      ¬(sf'.mem ⊨
        (ToBaseSpec.toSpec (spec mpl) (mpl.base (lib.fnBlockIdx fnName))).onPanic y
          (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf' ∗ R') := by
      intro _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ y code R' s0 sf', sf'.status = .Exited code →
      ¬(sf'.mem ⊨
        (ToBaseSpec.toSpec (spec mpl) (mpl.base (lib.fnBlockIdx fnName))).onExit y code
          (multiCodeROHookEntry lib mpl (lib.fnBlockIdx fnName) (lib.fnAddr mpl fnName) s0) sf' ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    HookOk (lib.codeROSubroutineHook mpl fnName externs overrides)
      (Spec.codeROMultiSubroutineHook lib mpl fnName spec) := by
  refine subroutineHook_ok_of_multiCodeRO h_pl h_sub
    (fun _ _ => Entails.refl _)
    (fun _ _ sf' hLf _ _ =>
      Entails.sepExists_right sf' (Entails.pure_right ⟨rfl, hLf⟩ (Entails.refl _)))
    h_ext1 h_no_panic h_no_exit

end ProofLib
