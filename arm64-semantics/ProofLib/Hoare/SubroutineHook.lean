/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Hooks
public import ProofLib.Hoare.Safety
public import ProofLib.SepLogic.WP.Defs
public import ProofLib.Invariant
public import ProofLib.Placed.Fetch
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model

/-!
# Verified Subroutines as Extern Hooks

Lifts verified `Program` and `Obj.MultiPlacedLib` subroutine contracts (`subroutine_ok`,
`subroutineOk`) to `HookOk` on `subroutineHook` and `MultiPlacedLib.subroutineHook`, via either
a writable `memRegion` code overlay (`loadCodeMem` and `restoreCodeMem` under `SepProp.NoRO`) or
`CodeLoaded` / read-only `codeRO` (`↦ᵣ`) witnesses. Also provides `SepWP` step rules for Linux
AArch64 anonymous read-write and `MAP_FIXED` `PROT_NONE` `SYS_MMAP` system calls.
-/

@[expose] public section

/-- Hook contract bundling `memRegion prog.base prog.code.length` with `spec` for
    `subroutineHook prog (prog.fnAddr name)`. A base-dependent `spec : BaseSpec β` (e.g. from a
    `c_spec` declaring `load_addr b`) is instantiated at the program's load base `prog.base`. -/
def Arm64.Spec.liftedSubroutineHook {S β : Type} [Arm64.ToBaseSpec S β] (prog : Arm64.Program)
    (name : String) (spec : S) : Arm64.Spec β where
  pre y s0 :=
    Arm64.memRegion prog.base prog.code.length ∗
      (Arm64.ToBaseSpec.toSpec spec prog.base).pre y
        (Arm64.subroutineHookEntry prog (prog.fnAddr name) s0)
  post y s0 sf :=
    ∃∗ sf', ⌜sf = Arm64.subroutineHookExit prog s0 sf'⌝ ∗
      (Arm64.memRegion prog.base prog.code.length ∗
        (Arm64.ToBaseSpec.toSpec spec prog.base).post y
          (Arm64.subroutineHookEntry prog (prog.fnAddr name) s0) sf')

/-- Hook contract bundling `⌜prog.CodeLoaded s0.mem⌝` with `spec` for
    `subroutineHook prog (prog.fnAddr name)`. Unlike `liftedSubroutineHook`, this does not consume
    writable `memRegion prog.base prog.code.length` or require `SepProp.NoRO`. -/
def Arm64.Spec.codeLoadedSubroutineHook {S β : Type} [Arm64.ToBaseSpec S β]
    (prog : Arm64.Program) (name : String) (spec : S) : Arm64.Spec β where
  pre y s0 :=
    ⌜prog.CodeLoaded s0.mem⌝ ∗
      (Arm64.ToBaseSpec.toSpec spec prog.base).pre y
        (Arm64.subroutineHookEntry prog (prog.fnAddr name) s0)
  post y s0 sf :=
    ∃∗ sf', ⌜sf = Arm64.subroutineHookExit prog s0 sf' ∧ prog.CodeLoaded sf.mem⌝ ∗
      (Arm64.ToBaseSpec.toSpec spec prog.base).post y
        (Arm64.subroutineHookEntry prog (prog.fnAddr name) s0) sf'
  onOom y s0 sf :=
    (Arm64.ToBaseSpec.toSpec spec prog.base).onOom y
      (Arm64.subroutineHookEntry prog (prog.fnAddr name) s0) sf

/-- Index of the block defining `fnName` in `lib` (`0` if `fnName` is not in any block). -/
def Arm64.Obj.MultiPlacedLib.fnBlockIdx (lib : Arm64.Obj.MultiPlacedLib)
    (fnName : String) : Nat :=
  match Arm64.Obj.lookupBlockSym fnName lib.blocks with
  | some (i, _) => i
  | none => 0

open Classical in
/-- State-transformer hook (`State → State`) induced by exported subroutine `fnName` of a
    multi-block placed library `lib` under placement `mpl`: dispatches on
    `Obj.lookupBlockSym fnName lib.blocks` to run `Arm64.subroutineHook` on the defining block's
    placed program `lib.blockProgram mpl i externs overrides` at `lib.fnAddr mpl fnName`,
    returning `id` if `fnName` is not defined in `lib.blocks`. -/
noncomputable def Arm64.Obj.MultiPlacedLib.subroutineHook (lib : Arm64.Obj.MultiPlacedLib)
    (mpl : Arm64.Obj.MultiPlacement) (fnName : String)
    (externs : String → Option (Arm64.State → Arm64.State) := fun _ => none)
    (overrides : String → Option (Arm64.State → Arm64.State) := fun _ => none) :
    Arm64.State → Arm64.State :=
  match Arm64.Obj.lookupBlockSym fnName lib.blocks with
  | some (i, _) =>
    Arm64.subroutineHook (lib.blockProgram mpl i externs overrides) (lib.fnAddr mpl fnName)
  | none => id

noncomputable abbrev Arm64.multiSubroutineHook := @Arm64.Obj.MultiPlacedLib.subroutineHook

/-- Hook contract bundling `⌜lib.CodeLoaded mpl s0.mem⌝` with
    `ToBaseSpec.toSpec (spec mpl) (mpl.base i)` across `subroutineHookEntry` /
    `subroutineHookExit` for `lib.subroutineHook mpl fnName externs overrides`, preserving
    `⌜lib.CodeLoaded mpl sf.mem⌝` in `post` and forwarding `onOom`. -/
def Arm64.Spec.codeLoadedMultiSubroutineHook {S β : Type} [Arm64.ToBaseSpec S β]
    (lib : Arm64.Obj.MultiPlacedLib) (mpl : Arm64.Obj.MultiPlacement)
    (fnName : String) (spec : Arm64.Obj.MultiPlacement → S)
    (externs : String → Option (Arm64.State → Arm64.State) := fun _ => none)
    (overrides : String → Option (Arm64.State → Arm64.State) := fun _ => none) :
    Arm64.Spec β :=
  let i := lib.fnBlockIdx fnName
  let prog := lib.blockProgram mpl i externs overrides
  let inner := Arm64.ToBaseSpec.toSpec (spec mpl) (mpl.base i)
  { pre := fun y s0 =>
      ⌜lib.CodeLoaded mpl s0.mem⌝ ∗
        inner.pre y (Arm64.subroutineHookEntry prog (lib.fnAddr mpl fnName) s0)
    post := fun y s0 sf =>
      ∃∗ sf', ⌜sf = Arm64.subroutineHookExit prog s0 sf' ∧ lib.CodeLoaded mpl sf.mem⌝ ∗
        inner.post y (Arm64.subroutineHookEntry prog (lib.fnAddr mpl fnName) s0) sf'
    onOom := fun y s0 sf =>
      inner.onOom y (Arm64.subroutineHookEntry prog (lib.fnAddr mpl fnName) s0) sf }

abbrev Arm64.Obj.MultiPlacedLib.codeLoadedSubroutineHook :=
  @Arm64.Spec.codeLoadedMultiSubroutineHook

/-- Every byte of `[base, base + len)` is mapped read-execute (`some Perm.rx`) and not marked
    `lazyFree` (`m.isLazyFree a = false`) in `m`. -/
def Arm64.Memory.RX (m : Arm64.Memory) (base : BitVec 64) (len : Nat) : Prop :=
  ∀ a : BitVec 64, Arm64.InRegion base len a →
    m.perm a = some Arm64.Perm.rx ∧ m.isLazyFree a = false

/-- Every block `i < lib.blocks.length` of `lib` has `Perm.rx` across its code range in `m`. -/
def Arm64.Obj.MultiPlacedLib.PermsRX (lib : Arm64.Obj.MultiPlacedLib)
    (mpl : Arm64.Obj.MultiPlacement) (m : Arm64.Memory) : Prop :=
  ∀ (i : Nat) (hi : i < lib.blocks.length), m.RX (mpl.base i) lib.blocks[i].code.length

/-- Read-only byte-slice assertion (`↦ᵣ`) owning block `i`'s relocated code bytes at `mpl.base i`. -/
def Arm64.Obj.MultiPlacedLib.blockCodeRO (lib : Arm64.Obj.MultiPlacedLib)
    (mpl : Arm64.Obj.MultiPlacement) (i : Nat) : Arm64.SepProp :=
  Arm64.pointsToBytesRO (mpl.base i) ((lib.blockLib i).text.patched (lib.blockPlacement mpl i))

/-- Separating conjunction of read-only (`↦ᵣ`) relocated code bytes across all blocks of `lib`. -/
def Arm64.Obj.MultiPlacedLib.codeRO (lib : Arm64.Obj.MultiPlacedLib)
    (mpl : Arm64.Obj.MultiPlacement) : Arm64.SepProp :=
  Arm64.Obj.sepAll ((List.range lib.blocks.length).map (lib.blockCodeRO mpl))

namespace ProofLib

open Arm64

/-! ## Code-Region Memory Overlay -/

private theorem loadCodeMem_cells_in {prog : Program} {m : Memory} {a : BitVec 64}
    (h : InRegion prog.base prog.code.length a) :
    (loadCodeMem prog m).cells a =
      if m.perm a == some Perm.rx && !m.isLazyFree a && m.read8 a == prog.code[(a - prog.base).toNat]'h
      then m.cells a
      else some (some { Perm.rx with anon := m.isAnon a }, prog.code[(a - prog.base).toNat]'h) := by
  simp only [loadCodeMem, h, ↓reduceDIte]

private theorem restoreCodeMem_cells_in {prog : Program} {m0 mf : Memory} {a : BitVec 64}
    (h : InRegion prog.base prog.code.length a) :
    (restoreCodeMem prog m0 mf).cells a =
      if mf.perm a == m0.perm a && mf.isLazyFree a == m0.isLazyFree a && mf.read8 a == m0.read8 a
      then mf.cells a else m0.cells a := by
  simp only [restoreCodeMem, h, ↓reduceIte]

theorem loadCodeMem_read8_in {prog : Program} {m : Memory} {a : BitVec 64}
    (h : InRegion prog.base prog.code.length a) :
    (loadCodeMem prog m).read8 a = prog.code[(a - prog.base).toNat]'h := by
  unfold Memory.read8; rw [loadCodeMem_cells_in h]
  by_cases hcond : (m.perm a == some Perm.rx && !m.isLazyFree a &&
      m.read8 a == prog.code[(a - prog.base).toNat]'h) = true
  · simp only [hcond, ↓reduceIte]
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact hcond.2
  · simp only [Bool.not_eq_true] at hcond; simp only [hcond, Bool.false_eq_true, ↓reduceIte]

theorem loadCodeMem_read8_out {prog : Program} {m : Memory} {a : BitVec 64}
    (h : ¬ InRegion prog.base prog.code.length a) :
    (loadCodeMem prog m).read8 a = m.read8 a := by
  simp [Memory.read8, loadCodeMem, h]

theorem loadCodeMem_perm_in {prog : Program} {m : Memory} {a : BitVec 64}
    (h : InRegion prog.base prog.code.length a) :
    (loadCodeMem prog m).perm a = some Perm.rx := by
  unfold Memory.perm; rw [loadCodeMem_cells_in h]
  by_cases hcond : (m.perm a == some Perm.rx && !m.isLazyFree a &&
      m.read8 a == prog.code[(a - prog.base).toNat]'h) = true
  · simp only [hcond, ↓reduceIte]
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact hcond.1.1
  · simp only [Bool.not_eq_true] at hcond; simp only [hcond, Bool.false_eq_true, ↓reduceIte]; rfl

theorem loadCodeMem_perm_out {prog : Program} {m : Memory} {a : BitVec 64}
    (h : ¬ InRegion prog.base prog.code.length a) :
    (loadCodeMem prog m).perm a = m.perm a := by
  simp [Memory.perm, loadCodeMem, h]

theorem loadCodeMem_isLazyFree_in {prog : Program} {m : Memory} {a : BitVec 64}
    (h : InRegion prog.base prog.code.length a) :
    (loadCodeMem prog m).isLazyFree a = false := by
  unfold Memory.isLazyFree; rw [loadCodeMem_cells_in h]
  by_cases hcond : (m.perm a == some Perm.rx && !m.isLazyFree a &&
      m.read8 a == prog.code[(a - prog.base).toNat]'h) = true
  · simp only [hcond, ↓reduceIte]
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hcond
    exact hcond.1.2
  · simp only [Bool.not_eq_true] at hcond; simp only [hcond, Bool.false_eq_true, ↓reduceIte]; rfl

theorem loadCodeMem_isLazyFree_out {prog : Program} {m : Memory} {a : BitVec 64}
    (h : ¬ InRegion prog.base prog.code.length a) :
    (loadCodeMem prog m).isLazyFree a = m.isLazyFree a := by
  simp [Memory.isLazyFree, loadCodeMem, h]

@[simp]
theorem loadCodeMem_isAnon (prog : Program) (m : Memory) (a : BitVec 64) :
    (loadCodeMem prog m).isAnon a = m.isAnon a := by
  by_cases h : InRegion prog.base prog.code.length a
  · unfold Memory.isAnon; rw [loadCodeMem_cells_in h]
    by_cases hcond : (m.perm a == some Perm.rx && !m.isLazyFree a &&
        m.read8 a == prog.code[(a - prog.base).toNat]'h) = true
    · simp only [hcond, ↓reduceIte]
    · simp only [Bool.not_eq_true] at hcond; simp only [hcond, Bool.false_eq_true, ↓reduceIte]; rfl
  · simp [Memory.isAnon, loadCodeMem, h]

theorem restoreCodeMem_isAnon_in_of_eq {prog : Program} {m0 mf : Memory} {a : BitVec 64}
    (h : InRegion prog.base prog.code.length a) (heq : mf.isAnon a = m0.isAnon a) :
    (restoreCodeMem prog m0 mf).isAnon a = m0.isAnon a := by
  unfold Memory.isAnon; rw [restoreCodeMem_cells_in h]
  by_cases hcond : (mf.perm a == m0.perm a && mf.isLazyFree a == m0.isLazyFree a &&
      mf.read8 a == m0.read8 a) = true
  · simp only [hcond, ↓reduceIte]; exact heq
  · simp only [Bool.not_eq_true] at hcond; simp only [hcond, Bool.false_eq_true, ↓reduceIte]

theorem restoreCodeMem_isAnon_in_true {prog : Program} {m0 mf : Memory} {a : BitVec 64}
    (h : InRegion prog.base prog.code.length a)
    (hm0 : m0.isAnon a = true) (hmf : mf.isAnon a = true) :
    (restoreCodeMem prog m0 mf).isAnon a = true := by
  unfold Memory.isAnon; rw [restoreCodeMem_cells_in h]
  by_cases hcond : (mf.perm a == m0.perm a && mf.isLazyFree a == m0.isLazyFree a &&
      mf.read8 a == m0.read8 a) = true
  · simp only [hcond, ↓reduceIte]; exact hmf
  · simp only [Bool.not_eq_true] at hcond; simp only [hcond, Bool.false_eq_true, ↓reduceIte]; exact hm0

theorem restoreCodeMem_read8_in {prog : Program} {m0 mf : Memory} {a : BitVec 64}
    (h : InRegion prog.base prog.code.length a) :
    (restoreCodeMem prog m0 mf).read8 a = m0.read8 a := by
  unfold Memory.read8; rw [restoreCodeMem_cells_in h]
  by_cases hcond : (mf.perm a == m0.perm a && mf.isLazyFree a == m0.isLazyFree a &&
      mf.read8 a == m0.read8 a) = true
  · simp only [hcond, ↓reduceIte]
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact hcond.2
  · simp only [Bool.not_eq_true] at hcond; simp only [hcond, Bool.false_eq_true, ↓reduceIte]

theorem restoreCodeMem_read8_out {prog : Program} {m0 mf : Memory} {a : BitVec 64}
    (h : ¬ InRegion prog.base prog.code.length a) :
    (restoreCodeMem prog m0 mf).read8 a = mf.read8 a := by
  simp [Memory.read8, restoreCodeMem, h]

theorem restoreCodeMem_perm_in {prog : Program} {m0 mf : Memory} {a : BitVec 64}
    (h : InRegion prog.base prog.code.length a) :
    (restoreCodeMem prog m0 mf).perm a = m0.perm a := by
  unfold Memory.perm; rw [restoreCodeMem_cells_in h]
  by_cases hcond : (mf.perm a == m0.perm a && mf.isLazyFree a == m0.isLazyFree a &&
      mf.read8 a == m0.read8 a) = true
  · simp only [hcond, ↓reduceIte]
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact hcond.1.1
  · simp only [Bool.not_eq_true] at hcond; simp only [hcond, Bool.false_eq_true, ↓reduceIte]

theorem restoreCodeMem_perm_out {prog : Program} {m0 mf : Memory} {a : BitVec 64}
    (h : ¬ InRegion prog.base prog.code.length a) :
    (restoreCodeMem prog m0 mf).perm a = mf.perm a := by
  simp [Memory.perm, restoreCodeMem, h]

theorem restoreCodeMem_isLazyFree_in {prog : Program} {m0 mf : Memory} {a : BitVec 64}
    (h : InRegion prog.base prog.code.length a) :
    (restoreCodeMem prog m0 mf).isLazyFree a = m0.isLazyFree a := by
  unfold Memory.isLazyFree; rw [restoreCodeMem_cells_in h]
  by_cases hcond : (mf.perm a == m0.perm a && mf.isLazyFree a == m0.isLazyFree a &&
      mf.read8 a == m0.read8 a) = true
  · simp only [hcond, ↓reduceIte]
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact hcond.1.2
  · simp only [Bool.not_eq_true] at hcond; simp only [hcond, Bool.false_eq_true, ↓reduceIte]

theorem restoreCodeMem_isLazyFree_out {prog : Program} {m0 mf : Memory} {a : BitVec 64}
    (h : ¬ InRegion prog.base prog.code.length a) :
    (restoreCodeMem prog m0 mf).isLazyFree a = mf.isLazyFree a := by
  simp [Memory.isLazyFree, restoreCodeMem, h]

theorem restoreCodeMem_isAnon_out {prog : Program} {m0 mf : Memory} {a : BitVec 64}
    (h : ¬ InRegion prog.base prog.code.length a) :
    (restoreCodeMem prog m0 mf).isAnon a = mf.isAnon a := by
  simp [Memory.isAnon, restoreCodeMem, h]

theorem restoreCodeMem_cells_in_of_perm_ne {prog : Program} {m0 mf : Memory} {a : BitVec 64}
    (h : InRegion prog.base prog.code.length a) (hne : mf.perm a ≠ m0.perm a) :
    (restoreCodeMem prog m0 mf).cells a = m0.cells a := by
  simp [restoreCodeMem, h, hne]

@[simp]
theorem restoreCodeMem_loadCodeMem (prog : Program) (m : Memory) :
    restoreCodeMem prog m (loadCodeMem prog m) = m := by
  ext a
  by_cases hin : InRegion prog.base prog.code.length a
  · simp only [restoreCodeMem, hin, ↓reduceIte]
    split
    · next hcond =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      have h1 : m.perm a = some Perm.rx := hcond.1.1.symm.trans (loadCodeMem_perm_in hin)
      have hlf : m.isLazyFree a = false := hcond.1.2.symm.trans (loadCodeMem_isLazyFree_in hin)
      have h2 : m.read8 a = prog.code[(a - prog.base).toNat]'hin :=
        hcond.2.symm.trans (loadCodeMem_read8_in hin)
      simp [loadCodeMem, hin, h1, hlf, h2]
    · rfl
  · simp [restoreCodeMem, loadCodeMem, hin]

theorem loadCodeMem_eq_of_codeLoaded {prog : Program} {m : Memory}
    (hL : prog.CodeLoaded m) :
    loadCodeMem prog m = m := by
  ext a
  by_cases hin : InRegion prog.base prog.code.length a
  · have hi : (a - prog.base).toNat < prog.code.length := hin
    have ha_eq : prog.base + BitVec.ofNat 64 (a - prog.base).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    have hr := hL.byte_eq (a - prog.base).toNat hi
    have hp := hL.perm_eq (a - prog.base).toNat hi
    have hlf := hL.isLazyFree_eq (a - prog.base).toNat hi
    rw [ha_eq] at hr hp hlf
    simp [loadCodeMem, hin, hr, hp, hlf]
  · simp [loadCodeMem, hin]

theorem restoreCodeMem_eq_of_codeLoaded {prog : Program} {m0 mf : Memory}
    (hL0 : prog.CodeLoaded m0) (hLf : prog.CodeLoaded mf) :
    restoreCodeMem prog m0 mf = mf := by
  ext a
  by_cases hin : InRegion prog.base prog.code.length a
  · have hi : (a - prog.base).toNat < prog.code.length := hin
    have ha_eq : prog.base + BitVec.ofNat 64 (a - prog.base).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    have hr0 := hL0.byte_eq (a - prog.base).toNat hi
    have hp0 := hL0.perm_eq (a - prog.base).toNat hi
    have hlf0 := hL0.isLazyFree_eq (a - prog.base).toNat hi
    have hrf := hLf.byte_eq (a - prog.base).toNat hi
    have hpf := hLf.perm_eq (a - prog.base).toNat hi
    have hlff := hLf.isLazyFree_eq (a - prog.base).toNat hi
    rw [ha_eq] at hr0 hp0 hlf0 hrf hpf hlff
    simp [restoreCodeMem, hin, hr0, hp0, hlf0, hrf, hpf, hlff]
  · simp [restoreCodeMem, hin]

theorem codeLoaded_loadCodeMem {prog : Program} (m : Memory)
    (h_al : prog.base.toNat % 4 = 0)
    (h_len : prog.base.toNat + prog.code.length ≤ 2 ^ 64) :
    prog.CodeLoaded (loadCodeMem prog m) := by
  refine Program.CodeLoaded.intro h_al h_len fun i hi => ?_
  have hi64 : i < 2 ^ 64 := Nat.lt_of_lt_of_le hi (Nat.le_trans (Nat.le_add_left _ _) h_len)
  have hsub_bv : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hsub : (prog.base + BitVec.ofNat 64 i - prog.base).toNat = i := by
    rw [hsub_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
  have hin : InRegion prog.base prog.code.length (prog.base + BitVec.ofNat 64 i) := by
    simpa [InRegion, hsub] using hi
  refine ⟨?_, loadCodeMem_perm_in hin, loadCodeMem_isLazyFree_in hin⟩
  rw [loadCodeMem_read8_in hin]
  congr 1

theorem keepsFrozen_restoreCodeMem {prog : Program} {m0 mf : Memory}
    (hk : (loadCodeMem prog m0).KeepsFrozen mf) :
    m0.KeepsFrozen (restoreCodeMem prog m0 mf) := by
  intro a hfrz
  by_cases hin : InRegion prog.base prog.code.length a
  · have hfrz' : (loadCodeMem prog m0).Frozen a := by
      unfold Memory.Frozen; rw [loadCodeMem_perm_in hin]; rfl
    obtain ⟨_, _, _, ha⟩ := hk a hfrz'
    rw [loadCodeMem_isAnon] at ha
    exact ⟨restoreCodeMem_read8_in hin, restoreCodeMem_perm_in hin,
      restoreCodeMem_isLazyFree_in hin, restoreCodeMem_isAnon_in_of_eq hin ha⟩
  · have hfrz' : (loadCodeMem prog m0).Frozen a := by
      unfold Memory.Frozen at hfrz ⊢; rwa [loadCodeMem_perm_out hin]
    obtain ⟨hr, hp, hlf, ha⟩ := hk a hfrz'
    rw [loadCodeMem_read8_out hin] at hr
    rw [loadCodeMem_perm_out hin] at hp
    rw [loadCodeMem_isLazyFree_out hin] at hlf
    rw [loadCodeMem_isAnon] at ha
    exact ⟨(restoreCodeMem_read8_out hin).trans hr, (restoreCodeMem_perm_out hin).trans hp,
      (restoreCodeMem_isLazyFree_out hin).trans hlf, (restoreCodeMem_isAnon_out hin).trans ha⟩

/-! ## `SepProp.NoRO` and Code-Region Framing -/

/-- A `SepProp` assertion contains no read-only (`.ro`) heap cells. Side condition of the
    cross-image bridge `subroutineHook_ok_with_codeRegion`. -/
def _root_.Arm64.SepProp.NoRO (P : SepProp) : Prop :=
  ∀ h a b, P h → h a ≠ some (.ro b)

section UnsealSepLogic

set_option allowUnsafeReducibility true
attribute [local semireducible]
  Heap.empty Heap.singleton Heap.singletonRO Heap.singletonProtNone Heap.singletonLazy
  Heap.Disjoint Heap.union Heap.Matches
  SepProp.Satisfies SepProp.Entails SepProp.emp SepProp.pure SepProp.sepConj SepProp.sepExists
  ghostMapAuth ghostMapElem ghostMapAuthHeap ghostMapElemHeap
  pointsTo8 pointsToBytes pointsTo16 pointsTo32 pointsTo64 pointsTo128 pointsToWords64
  pointsTo8Lazy pointsTo16Lazy pointsTo32Lazy pointsTo64Lazy pointsTo128Lazy
  pointsTo8ProtNone pointsToBytesProtNone
  regionHeap regionHeapRO regionHeapProtNone regionHeapLazy regionBlock regionBlockProtNone
  memRegion memRegionProtNone memRegionLazy mappedHeap memMapped

namespace SepProp.NoRO

@[simp]
theorem emp : SepProp.NoRO SepProp.emp := by
  intro h a b hp; rw [SepProp.holds_emp_iff] at hp; subst hp; simp [Heap.empty]

@[simp]
theorem pure (φ : Prop) : SepProp.NoRO ⌜φ⌝ := by
  intro h a b hp; obtain ⟨rfl, _⟩ := SepProp.holds_pure_iff.1 hp; simp [Heap.empty]

@[simp]
theorem pointsTo8 (x : BitVec 64) (v : BitVec 8) : SepProp.NoRO (x ↦₈ v) := by
  intro h a b hp; rw [holds_pointsTo8_iff] at hp; subst hp; simp [Heap.singleton]

@[simp]
theorem pointsTo8ProtNone (x : BitVec 64) (v : BitVec 8) : SepProp.NoRO (x ↦₈ₙ v) := by
  intro h a b hp; rw [holds_pointsTo8ProtNone_iff] at hp; subst hp; simp [Heap.singletonProtNone]

@[simp]
theorem pointsTo8Lazy (x : BitVec 64) : SepProp.NoRO (x ↦₈ₗ) := by
  intro h a b hp; rw [holds_pointsTo8Lazy_iff] at hp; subst hp; simp [Heap.singletonLazy]

@[simp]
theorem sepConj {P Q : SepProp} (hP : SepProp.NoRO P) (hQ : SepProp.NoRO Q) :
    SepProp.NoRO (P ∗ Q) := by
  intro h a b hp; obtain ⟨h1, h2, _, rfl, hp1, hp2⟩ := SepProp.holds_sepConj_iff.1 hp
  simp only [Heap.union]
  cases h1a : h1 a with
  | none => exact hQ h2 a b hp2
  | some c =>
    intro heq; injection heq with hc; subst hc
    exact hP h1 a b hp1 h1a

@[simp]
theorem pointsTo16 (x : BitVec 64) (v : BitVec 16) : SepProp.NoRO (x ↦₁₆ v) := by
  unfold Arm64.pointsTo16; exact sepConj (pointsTo8 _ _) (pointsTo8 _ _)

@[simp]
theorem pointsTo32 (x : BitVec 64) (v : BitVec 32) : SepProp.NoRO (x ↦₃₂ v) := by
  unfold Arm64.pointsTo32
  exact sepConj (pointsTo8 _ _) (sepConj (pointsTo8 _ _) (sepConj (pointsTo8 _ _) (pointsTo8 _ _)))

@[simp]
theorem pointsTo64 (x : BitVec 64) (v : BitVec 64) : SepProp.NoRO (x ↦₆₄ v) := by
  unfold Arm64.pointsTo64
  exact sepConj (pointsTo8 _ _) (sepConj (pointsTo8 _ _) (sepConj (pointsTo8 _ _)
    (sepConj (pointsTo8 _ _) (sepConj (pointsTo8 _ _) (sepConj (pointsTo8 _ _)
      (sepConj (pointsTo8 _ _) (pointsTo8 _ _)))))))

@[simp]
theorem pointsTo128 (x : BitVec 64) (v : BitVec 128) : SepProp.NoRO (x ↦₁₂₈ v) := by
  unfold Arm64.pointsTo128; exact sepConj (pointsTo64 _ _) (pointsTo64 _ _)

@[simp]
theorem pointsToBytes (x : BitVec 64) (bs : List (BitVec 8)) : SepProp.NoRO (x ↦ₛ bs) := by
  induction bs generalizing x with
  | nil => rw [pointsToBytes_nil]; exact emp
  | cons b bs ih => rw [pointsToBytes_cons]; exact sepConj (pointsTo8 _ _) (ih _)

@[simp]
theorem pointsToBytesProtNone (x : BitVec 64) (bs : List (BitVec 8)) :
    SepProp.NoRO (x ↦ₙ bs) := by
  induction bs generalizing x with
  | nil => rw [pointsToBytesProtNone_nil_def]; exact emp
  | cons b bs ih =>
    rw [pointsToBytesProtNone_cons_def]; exact sepConj (pointsTo8ProtNone _ _) (ih _)

@[simp]
theorem pointsToWords64 (x : BitVec 64) (ws : List (BitVec 64)) : SepProp.NoRO (x ↦₆₄* ws) := by
  induction ws generalizing x with
  | nil => rw [pointsToWords64_nil]; exact emp
  | cons w ws ih => rw [pointsToWords64_cons]; exact sepConj (pointsTo64 _ _) (ih _)

@[simp]
theorem regionBlock (base : BitVec 64) (len : Nat) (m : Memory) :
    SepProp.NoRO (Arm64.regionBlock base len m) := by
  intro h a b hp; rw [holds_regionBlock_iff] at hp; subst hp; simp [Arm64.regionHeap]

@[simp]
theorem regionBlockProtNone (base : BitVec 64) (len : Nat) (m : Memory) :
    SepProp.NoRO (Arm64.regionBlockProtNone base len m) := by
  intro h a b hp; rw [holds_regionBlockProtNone_iff] at hp; subst hp
  simp [Arm64.regionHeapProtNone]

@[simp]
theorem sepExists {α : Sort _} {P : α → SepProp} (hP : ∀ x, SepProp.NoRO (P x)) :
    SepProp.NoRO (∃∗ x, P x) := by
  intro h a b hp; obtain ⟨x, hx⟩ := SepProp.holds_sepExists_iff.1 hp; exact hP x h a b hx

@[simp]
theorem memRegion (base : BitVec 64) (len : Nat) : SepProp.NoRO (Arm64.memRegion base len) := by
  intro h a b hp; obtain ⟨m, rfl⟩ := holds_memRegion_iff.1 hp
  exact regionBlock base len m _ a b (holds_regionBlock_iff.2 rfl)

@[simp]
theorem memRegionProtNone (base : BitVec 64) (len : Nat) :
    SepProp.NoRO (Arm64.memRegionProtNone base len) := by
  intro h a b hp; obtain ⟨m, rfl⟩ := holds_memRegionProtNone_iff.1 hp
  exact regionBlockProtNone base len m _ a b (holds_regionBlockProtNone_iff.2 rfl)

@[simp]
theorem memRegionLazy (base : BitVec 64) (len : Nat) :
    SepProp.NoRO (Arm64.memRegionLazy base len) := by
  intro h a b hp; rw [holds_memRegionLazy_iff] at hp; subst hp; simp [Arm64.regionHeapLazy]

@[simp]
theorem pointsTo16Lazy (x : BitVec 64) : SepProp.NoRO (x ↦₁₆ₗ) := by
  unfold Arm64.pointsTo16Lazy; exact sepConj (pointsTo8Lazy _) (pointsTo8Lazy _)

@[simp]
theorem pointsTo32Lazy (x : BitVec 64) : SepProp.NoRO (x ↦₃₂ₗ) := by
  unfold Arm64.pointsTo32Lazy
  exact sepConj (pointsTo8Lazy _) (sepConj (pointsTo8Lazy _) (sepConj (pointsTo8Lazy _) (pointsTo8Lazy _)))

@[simp]
theorem pointsTo64Lazy (x : BitVec 64) : SepProp.NoRO (x ↦₆₄ₗ) := by
  unfold Arm64.pointsTo64Lazy
  exact sepConj (pointsTo8Lazy _) (sepConj (pointsTo8Lazy _) (sepConj (pointsTo8Lazy _)
    (sepConj (pointsTo8Lazy _) (sepConj (pointsTo8Lazy _) (sepConj (pointsTo8Lazy _)
      (sepConj (pointsTo8Lazy _) (pointsTo8Lazy _)))))))

@[simp]
theorem pointsTo128Lazy (x : BitVec 64) : SepProp.NoRO (x ↦₁₂₈ₗ) := by
  unfold Arm64.pointsTo128Lazy; exact sepConj (pointsTo64Lazy _) (pointsTo64Lazy _)

@[simp]
theorem memMapped (base : BitVec 64) (len : Nat) : SepProp.NoRO (Arm64.memMapped base len) := by
  intro h a b hp
  rw [holds_memMapped_iff] at hp
  subst hp
  nofun

@[simp]
theorem ite {c : Prop} [Decidable c] {P Q : SepProp}
    (hP : SepProp.NoRO P) (hQ : SepProp.NoRO Q) :
    SepProp.NoRO (if c then P else Q) := by
  split <;> assumption

@[simp]
theorem ghostMapAuth (γ : GhostName) (L : BitVec 64 → Option Nat) :
    SepProp.NoRO (ProofLib.ghostMapAuth γ L) := by
  intro h a b hp
  subst hp
  nofun

@[simp]
theorem ghostMapElem (γ : GhostName) (p : BitVec 64) (n : Nat) :
    SepProp.NoRO (ProofLib.ghostMapElem γ p n) := by
  intro h a b hp
  subst hp
  nofun

end SepProp.NoRO

theorem Heap.eq_none_of_disjoint_regionHeap {base : BitVec 64} {len : Nat} {m : Memory}
    {h : Heap} (hd : (regionHeap base len m).Disjoint h)
    {a : BitVec 64} (hin : InRegion base len a) :
    h a = none := by
  have hc : (regionHeap base len m).phys a = some (.rw (m.read8 a)) := by simp [regionHeap, hin]
  rcases hd.1 a with h1 | h2 | ⟨b, h1, _⟩
  · rw [hc] at h1; cases h1
  · exact h2
  · rw [hc] at h1; cases h1

theorem Heap.Matches.loadCodeMem_of_eq_none {prog : Program} {m : Memory} {h : Heap}
    (hm : h.Matches m)
    (hnone : ∀ a, InRegion prog.base prog.code.length a → h a = none) :
    h.Matches (loadCodeMem prog m) := by
  refine ⟨fun a c hac => ?_, hm.2.1, fun a hmap => ?_⟩
  · have hout : ¬ InRegion prog.base prog.code.length a := fun hin => by
      have hna : h.phys a = none := hnone a hin
      rw [hna] at hac; contradiction
    have hc := hm.1 a c hac
    cases c <;>
      simp only [loadCodeMem_read8_out hout, loadCodeMem_perm_out hout, loadCodeMem_isLazyFree_out hout] <;>
      exact hc
  · by_cases hin : InRegion prog.base prog.code.length a
    · rw [loadCodeMem_perm_in hin, loadCodeMem_isAnon]
      exact ⟨rfl, (hm.2.2 a hmap).2⟩
    · rw [loadCodeMem_perm_out hin, loadCodeMem_isAnon]
      exact hm.2.2 a hmap

theorem Heap.Matches.restoreCodeMem_of_eq_none {prog : Program} {m0 mf : Memory} {h : Heap}
    (hm : h.Matches mf)
    (hnone : ∀ a, InRegion prog.base prog.code.length a → h a = none)
    (hm0 : ∀ a, InRegion prog.base prog.code.length a → h.mapped a = true →
      (m0.perm a).mapped = true ∧ m0.isAnon a = true) :
    h.Matches (restoreCodeMem prog m0 mf) := by
  refine ⟨fun a c hac => ?_, hm.2.1, fun a hmap => ?_⟩
  · have hout : ¬ InRegion prog.base prog.code.length a := fun hin => by
      have hna : h.phys a = none := hnone a hin
      rw [hna] at hac; contradiction
    have hc := hm.1 a c hac
    cases c <;>
      simp only [restoreCodeMem_read8_out hout, restoreCodeMem_perm_out hout,
        restoreCodeMem_isLazyFree_out hout] <;>
      exact hc
  · by_cases hin : InRegion prog.base prog.code.length a
    · rw [restoreCodeMem_perm_in hin]
      exact ⟨(hm0 a hin hmap).1,
        restoreCodeMem_isAnon_in_true hin (hm0 a hin hmap).2 (hm.2.2 a hmap).2⟩
    · rw [restoreCodeMem_perm_out hin, restoreCodeMem_isAnon_out hin]
      exact hm.2.2 a hmap

/-- Every cell of a `NoRO` heap matching a `CodeLoaded` memory is `none` on the code region
    `InRegion prog.base prog.code.length` (where permissions are `Perm.rx`, distinct from
    `Perm.rw` and `Perm.protNone`). -/
theorem Heap.eq_none_of_noRO_codeLoaded {prog : Program} {m : Memory} {P : SepProp} {h : Heap}
    (hP : P h) (hno : SepProp.NoRO P) (hm : h.Matches m) (hL : prog.CodeLoaded m)
    {a : BitVec 64} (hin : InRegion prog.base prog.code.length a) :
    h a = none := by
  have hi : (a - prog.base).toNat < prog.code.length := hin
  have ha_eq : prog.base + BitVec.ofNat 64 (a - prog.base).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  have hperm : m.perm a = some Perm.rx := by
    rw [← ha_eq]
    exact hL.perm_eq (a - prog.base).toNat hi
  cases hc : h.phys a with
  | none => rfl
  | some cell =>
    cases cell with
    | rw b =>
      have ⟨_, hprw, _⟩ := hm.1 a (.rw b) hc
      rw [hperm] at hprw; cases hprw
    | ro b =>
      exact False.elim (hno h a b hP hc)
    | protNone b =>
      have ⟨_, hpn, _⟩ := hm.1 a (.protNone b) hc
      rw [hperm] at hpn; cases hpn
    | lazy =>
      have hprw := hm.1 a .lazy hc
      rw [hperm] at hprw; cases hprw
    | protNoneLazy =>
      have hpn := hm.1 a .protNoneLazy hc
      rw [hperm] at hpn; cases hpn

/-! ## Deterministic `subroutineHook` Construction -/

@[simp]
theorem subroutineHookEntry_symtab (prog : Program) (entry_pc : BitVec 64) (s0 : State) :
    (subroutineHookEntry prog entry_pc s0).symtab = s0.symtab := rfl

@[simp]
theorem subroutineHookEntry_sp (prog : Program) (entry_pc : BitVec 64) (s0 : State) :
    (subroutineHookEntry prog entry_pc s0).sp = s0.sp := rfl

@[simp]
theorem subroutineHookEntry_readReg64 (prog : Program) (entry_pc : BitVec 64) (s0 : State)
    (r : Reg) (hr : r ≠ .lr := by decide) :
    (subroutineHookEntry prog entry_pc s0).readReg64 r = s0.readReg64 r := by
  simp [subroutineHookEntry, hr]

@[simp]
theorem subroutineHookExit_mem (prog : Program) (s0 sf' : State) :
    (subroutineHookExit prog s0 sf').mem = restoreCodeMem prog s0.mem sf'.mem := rfl

@[simp]
theorem subroutineHookExit_symtab (prog : Program) (s0 sf' : State) :
    (subroutineHookExit prog s0 sf').symtab = sf'.symtab := by
  unfold subroutineHookExit
  dsimp only
  split <;> rfl

@[simp]
theorem subroutineHookExit_sp (prog : Program) (s0 sf' : State) :
    (subroutineHookExit prog s0 sf').sp = sf'.sp := by
  unfold subroutineHookExit
  dsimp only
  split <;> rfl

@[simp]
theorem subroutineHookExit_readReg64 (prog : Program) (s0 sf' : State)
    (r : Reg) (hr : r ≠ .lr := by decide) :
    (subroutineHookExit prog s0 sf').readReg64 r = sf'.readReg64 r := by
  unfold subroutineHookExit
  dsimp only
  split <;> simp [hr]

open Classical in
theorem subroutineHook_eq_of_stepsUntil {prog : Program} {entry_pc : BitVec 64}
    {s0 sf' : State}
    (h_until : StepsUntil prog (SubroutineStop (subroutineHookEntry prog entry_pc s0))
      (subroutineHookEntry prog entry_pc s0) sf')
    (h_stop : SubroutineStop (subroutineHookEntry prog entry_pc s0) sf') :
    subroutineHook prog entry_pc s0 = subroutineHookExit prog s0 sf' := by
  have hex : ∃ sf, StepsUntil prog (SubroutineStop (subroutineHookEntry prog entry_pc s0))
      (subroutineHookEntry prog entry_pc s0) sf ∧
      SubroutineStop (subroutineHookEntry prog entry_pc s0) sf :=
    ⟨sf', h_until, h_stop⟩
  simp only [subroutineHook, hex, ↓reduceDIte]
  congr 1
  exact StepsUntil.deterministic (Classical.choose_spec hex).1 (Classical.choose_spec hex).2
    h_until h_stop

private theorem base_add_one_mod_four_ne_zero {base : BitVec 64} (h_al : base.toNat % 4 = 0) :
    (base + 1#64).toNat % 4 ≠ 0 := by
  have h1 : (base + 1#64).toNat = (base.toNat + 1) % 2 ^ 64 := BitVec.toNat_add base 1#64
  omega

private theorem fetchMem_base_add_one {prog : Program} (m : Memory)
    (h_al : prog.base.toNat % 4 = 0) :
    prog.fetchMem m (prog.base + 1#64) = none := by
  have hmod := base_add_one_mod_four_ne_zero h_al
  simp only [Program.fetchMem, hmod, ne_eq, not_false_eq_true, ↓reduceIte, ite_self]

/-- Any `Steps` execution from `subroutineHookEntry prog entry_pc s0` ending in a
    `SubroutineOutcome` state `sf'` is the unique first `SubroutineStop` state, so
    `subroutineHook prog entry_pc s0 = subroutineHookExit prog s0 sf'`. -/
theorem subroutineHook_eq_of_steps_outcome {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α} {x : α} {R' : SepProp} {s0 sf' : State}
    (h_al : prog.base.toNat % 4 = 0)
    (h_ext1 : prog.externAt? (prog.base + 1#64) = none)
    (h_steps : Steps prog (subroutineHookEntry prog entry_pc s0) sf')
    (hout : SubroutineOutcome spec x R' (subroutineHookEntry prog entry_pc s0) sf') :
    subroutineHook prog entry_pc s0 = subroutineHookExit prog s0 sf' := by
  have hlr : (subroutineHookEntry prog entry_pc s0).readReg64 Reg.lr = prog.base + 1#64 := rfl
  have h_until := stepsUntil_of_steps_subroutineOutcome_sentinel_lr
    (fun m => hlr ▸ fetchMem_base_add_one m h_al) (hlr ▸ h_ext1) h_steps hout
  exact subroutineHook_eq_of_stepsUntil h_until hout.to_subroutineStop

/-! ## `Program` Subroutine-to-Hook Bridges -/

theorem subroutineHookExit_returned {prog : Program} {entry_pc : BitVec 64} {s0 sf' : State}
    (hret : Returned (subroutineHookEntry prog entry_pc s0) sf') :
    Returned s0 (subroutineHookExit prog s0 sf') := by
  rcases hret with ⟨hpc, hsp, hrun⟩
  have hpc' : sf'.pc = prog.base + 1#64 := by
    simpa [subroutineHookEntry, State.setMem, State.setPC, State.writeReg64, State.readReg64,
      Reg.lr] using hpc
  have hsp' : sf'.sp = s0.sp := by
    simpa [subroutineHookEntry, State.setMem, State.setPC, State.writeReg64] using hsp
  simp [Returned, subroutineHookExit, hpc', hrun, hsp', State.setMem, State.setPC, State.writeReg64]

@[simp, arm64_norm]
theorem calleeSavedVRegs_subroutineHookEntry (prog : Program) (entry_pc : BitVec 64) (s0 : State) :
    calleeSavedVRegs (subroutineHookEntry prog entry_pc s0) = calleeSavedVRegs s0 := by
  cases s0; rfl

@[simp, arm64_norm]
theorem calleeSavedVRegs_subroutineHookExit (prog : Program) (s0 sf' : State) :
    calleeSavedVRegs (subroutineHookExit prog s0 sf') = calleeSavedVRegs sf' := by
  unfold subroutineHookExit; dsimp only; split <;> (cases sf'; rfl)

theorem subroutineHookExit_cc {prog : Program} {entry_pc : BitVec 64} {s0 sf' : State}
    (hcc : CallingConventionPreserved (subroutineHookEntry prog entry_pc s0) sf') :
    CallingConventionPreserved s0 (subroutineHookExit prog s0 sf') := by
  rcases hcc with ⟨hsp, hcs⟩
  have hsp' : sf'.sp = s0.sp := by
    simpa [subroutineHookEntry, State.setMem, State.setPC, State.writeReg64] using hsp
  refine ⟨?_, ?_⟩
  · unfold subroutineHookExit
    dsimp only
    split <;> simp [hsp', State.setMem, State.setPC, State.writeReg64]
  · simp only [CalleeSavedPreserved, subroutineHookEntry, State.setMem, State.setPC,
      State.writeReg64, State.readReg64] at hcs
    unfold subroutineHookExit
    dsimp only
    split <;> (simp only [CalleeSavedPreserved, State.setMem, State.setPC, State.writeReg64,
      State.readReg64]; exact hcs)

theorem restoreCodeMem_satisfies_true_sepConj {prog : Program} {s0 sf' : State}
    {P R : SepProp} {h_R : Heap}
    (hR_sat : R h_R)
    (hR_none : ∀ a, InRegion prog.base prog.code.length a → h_R a = none ∧
      (h_R.mapped a = true → (s0.mem.perm a).mapped = true ∧ s0.mem.isAnon a = true))
    (hq : sf'.mem ⊨ P ∗ ⟨fun h => h = h_R⟩) :
    (subroutineHookExit prog s0 sf').mem ⊨ ⌜True⌝ ∗ R := by
  obtain ⟨_, hq', hmf'⟩ := SepProp.satisfies_iff.1 hq
  rcases SepProp.holds_sepConj_iff.1 hq' with ⟨hp, h_R', hd, rfl, _, hR'_eq⟩
  rw [hR'_eq] at hd hmf'
  have hm_R' : h_R.Matches sf'.mem := Heap.Matches.of_union_right hd hmf'
  have hm_R_f : h_R.Matches (subroutineHookExit prog s0 sf').mem := by
    rw [subroutineHookExit_mem]
    exact Heap.Matches.restoreCodeMem_of_eq_none hm_R' (fun a ha => (hR_none a ha).1)
      (fun a ha hmp => (hR_none a ha).2 hmp)
  rw [satisfies_pure_sepConj]
  exact ⟨trivial, SepProp.satisfies_iff.2 ⟨h_R, hR_sat, hm_R_f⟩⟩

/-- Lift `subroutine_ok prog entry_pc innerSpec` to `HookOk (subroutineHook prog entry_pc) spec`
    when `spec` frames `memRegion prog.base prog.code.length` around `innerSpec`. -/
theorem subroutineHook_ok_with_codeRegion {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {innerSpec spec : Spec α}
    (h_al : prog.base.toNat % 4 = 0)
    (h_len : prog.base.toNat + prog.code.length ≤ 2 ^ 64)
    (h_ext1 : prog.externAt? (prog.base + 1#64) = none)
    (h_sub : subroutine_ok prog entry_pc innerSpec)
    (h_pre : ∀ x s0,
      spec.pre x s0 ⊢
        memRegion prog.base prog.code.length ∗
        innerSpec.pre x (subroutineHookEntry prog entry_pc s0))
    (h_post : ∀ x s0 sf',
      (memRegion prog.base prog.code.length ∗
        innerSpec.post x (subroutineHookEntry prog entry_pc s0) sf') ⊢
        spec.post x s0 (subroutineHookExit prog s0 sf'))
    (h_noRO : ∀ x s0 sf',
      SepProp.NoRO (innerSpec.post x (subroutineHookEntry prog entry_pc s0) sf'))
    (h_no_panic : ∀ x R' s0 sf', sf'.status = .Panicked →
      ¬(sf'.mem ⊨ innerSpec.onPanic x (subroutineHookEntry prog entry_pc s0) sf' ∗ R') := by
      intro _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ x code R' s0 sf', sf'.status = .Exited code →
      ¬(sf'.mem ⊨ innerSpec.onExit x code (subroutineHookEntry prog entry_pc s0) sf' ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ x (R : SepProp) (h_R : Heap) s0 sf',
      R h_R →
      (∀ a, InRegion prog.base prog.code.length a → h_R a = none ∧
        (h_R.mapped a = true → (s0.mem.perm a).mapped = true ∧ s0.mem.isAnon a = true)) →
      sf'.status = .OutOfMemory →
      (sf'.mem ⊨ innerSpec.onOom x (subroutineHookEntry prog entry_pc s0) sf' ∗ ⟨fun h => h = h_R⟩) →
      ((subroutineHookExit prog s0 sf').mem ⊨ spec.onOom x s0 (subroutineHookExit prog s0 sf') ∗ R) := by
      intro _ _ _ _ _ hR_sat hR_none _ ho
      try simp only [Spec.liftedSubroutineHook, Spec.allowOom] at ho ⊢
      first
      | exact False.elim (not_satisfies_false_sepConj ho)
      | exact restoreCodeMem_satisfies_true_sepConj hR_sat hR_none ho) :
    HookOk (subroutineHook prog entry_pc) spec := by
  intro x R s0 hrun hpre_sat hsp
  have hpre_framed : s0.mem ⊨
      (memRegion prog.base prog.code.length ∗
        innerSpec.pre x (subroutineHookEntry prog entry_pc s0)) ∗ R :=
    Satisfies.mono (sepConj_mono_left (h_pre x s0)) hpre_sat
  rw [sepConj_assoc] at hpre_framed
  obtain ⟨_, hpf, hm0⟩ := SepProp.satisfies_iff.1 hpre_framed
  obtain ⟨h_code, h_rest, hd_code_rest, rfl, hcode, hrest⟩ := SepProp.holds_sepConj_iff.1 hpf
  obtain ⟨m_w, rfl⟩ := holds_memRegion_iff.1 hcode
  obtain ⟨h_in, h_R, hd_in_R, rfl, hin_pre, hR_sat⟩ := SepProp.holds_sepConj_iff.1 hrest
  have hm_code : (regionHeap prog.base prog.code.length m_w).Matches s0.mem :=
    Heap.Matches.of_union_left hm0
  have hm0_rw : ∀ a, InRegion prog.base prog.code.length a → s0.mem.perm a = some Perm.rw := by
    intro a ha
    have hc : (regionHeap prog.base prog.code.length m_w).phys a = some (.rw (m_w.read8 a)) := by
      simp [regionHeap, ha]
    exact (hm_code.1 a _ hc).2.1
  have hm0_mapped : ∀ a, InRegion prog.base prog.code.length a → (s0.mem.perm a).mapped = true := by
    intro a ha; rw [hm0_rw a ha]; rfl
  have hm_rest : (h_in.union h_R).Matches s0.mem :=
    Heap.Matches.of_union_right hd_code_rest hm0
  have hm_in : h_in.Matches s0.mem := Heap.Matches.of_union_left hm_rest
  have hm_R : h_R.Matches s0.mem := Heap.Matches.of_union_right hd_in_R hm_rest
  have ⟨hd_code_in, hd_code_R⟩ := (Heap.disjoint_union_right hd_in_R).1 hd_code_rest
  have hin_none : ∀ a, InRegion prog.base prog.code.length a → h_in a = none :=
    fun a ha => Heap.eq_none_of_disjoint_regionHeap hd_code_in ha
  have hR_none : ∀ a, InRegion prog.base prog.code.length a → h_R a = none :=
    fun a ha => Heap.eq_none_of_disjoint_regionHeap hd_code_R ha
  let s0' := subroutineHookEntry prog entry_pc s0
  let R_sing : SepProp := ⟨fun h => h = h_R⟩
  have hs0'_pre : s0'.mem ⊨ innerSpec.pre x s0' ∗ R_sing := by
    refine SepProp.satisfies_iff.2 ⟨h_in.union h_R,
      SepProp.holds_sepConj_iff.2 ⟨h_in, h_R, hd_in_R, rfl, hin_pre, rfl⟩, ?_⟩
    exact Heap.Matches.union (Heap.Matches.loadCodeMem_of_eq_none hm_in hin_none)
      (Heap.Matches.loadCodeMem_of_eq_none hm_R hR_none)
  have hL0 : prog.CodeLoaded s0'.mem := codeLoaded_loadCodeMem s0.mem h_al h_len
  have hs0'_pc : s0'.pc = entry_pc := rfl
  have hs0'_run : s0'.status = .Running := hrun
  have hs0'_sp : s0'.spAligned = true := by
    simpa [s0', subroutineHookEntry, State.spAligned, State.setMem, State.setPC,
      State.writeReg64] using hsp
  obtain ⟨sf', h_steps, hout⟩ := reaches_outcome_iff.1 (subroutine_ok_iff.1 h_sub x R_sing s0' hs0'_pc hs0'_run hs0'_pre hs0'_sp) hL0
  have hLf_all : prog.CodeLoaded sf'.mem := h_steps.codeLoaded hL0
  have hsf_cells_in : ∀ a, InRegion prog.base prog.code.length a →
      (restoreCodeMem prog s0.mem sf'.mem).cells a = s0.mem.cells a := by
    intro a ha
    have hi : (a - prog.base).toNat < prog.code.length := ha
    have ha_eq : prog.base + BitVec.ofNat 64 (a - prog.base).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have hpf : sf'.mem.perm a = some Perm.rx := by
      rw [← ha_eq]; exact hLf_all.perm_eq (a - prog.base).toNat hi
    refine restoreCodeMem_cells_in_of_perm_ne ha ?_
    rw [hpf, hm0_rw a ha]; decide
  have hhook_eq : subroutineHook prog entry_pc s0 = subroutineHookExit prog s0 sf' :=
    subroutineHook_eq_of_steps_outcome h_al h_ext1 h_steps hout
  rw [hhook_eq]
  rcases hout with ⟨hret, hcc, hpost_sat⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine ⟨keepsFrozen_restoreCodeMem h_steps.keepsFrozen, ?_, Or.inl ⟨
      subroutineHookExit_returned hret, subroutineHookExit_cc hcc, ?_⟩⟩
    · rw [subroutineHookExit_symtab, h_steps.symtab_eq, subroutineHookEntry_symtab]
    · obtain ⟨_, hps, hmf'⟩ := SepProp.satisfies_iff.1 hpost_sat
      rcases SepProp.holds_sepConj_iff.1 hps with ⟨hp_post, h_R', hd_post_R, rfl, hpost_in, hR'_eq⟩
      dsimp only [R_sing] at hR'_eq
      rw [hR'_eq] at hd_post_R hmf'
      have hm_post : hp_post.Matches sf'.mem := Heap.Matches.of_union_left hmf'
      have hm_R' : h_R.Matches sf'.mem := Heap.Matches.of_union_right hd_post_R hmf'
      have hpost_none : ∀ a, InRegion prog.base prog.code.length a → hp_post a = none :=
        fun a ha => Heap.eq_none_of_noRO_codeLoaded hpost_in (h_noRO x s0 sf') hm_post hLf_all ha
      have hd_code_post : (regionHeap prog.base prog.code.length m_w).Disjoint hp_post := by
        refine Heap.Disjoint.of_phys_left rfl rfl fun a => ?_
        by_cases ha : InRegion prog.base prog.code.length a
        · exact Or.inr (Or.inl (hpost_none a ha))
        · exact Or.inl (by simp [regionHeap, ha])
      have hd_code_postR :
          (regionHeap prog.base prog.code.length m_w).Disjoint (hp_post.union h_R) :=
        (Heap.disjoint_union_right hd_post_R).2 ⟨hd_code_post, hd_code_R⟩
      have hm_code_f :
          (regionHeap prog.base prog.code.length m_w).Matches
            (subroutineHookExit prog s0 sf').mem := by
        refine Heap.Matches.of_phys rfl rfl fun a c hac => ?_
        have ha : InRegion prog.base prog.code.length a :=
          Classical.byContradiction fun hna => by simp [regionHeap, hna] at hac
        have hmc := hm_code.1 a c hac
        have hcell := hsf_cells_in a ha
        cases c <;>
          simp only [subroutineHookExit_mem, Memory.read8, Memory.perm, Memory.isLazyFree, hcell] <;>
          exact hmc
      have hm_post_f : hp_post.Matches (subroutineHookExit prog s0 sf').mem := by
        rw [subroutineHookExit_mem]
        refine Heap.Matches.restoreCodeMem_of_eq_none hm_post hpost_none fun a ha hmp =>
          ⟨hm0_mapped a ha, ?_⟩
        have hfrz_in : (loadCodeMem prog s0.mem).Frozen a := by
          unfold Memory.Frozen; rw [loadCodeMem_perm_in ha]; rfl
        have hanon_eq : sf'.mem.isAnon a = s0.mem.isAnon a :=
          (h_steps.keepsFrozen a hfrz_in).2.2.2.trans (loadCodeMem_isAnon prog s0.mem a)
        exact hanon_eq.symm.trans (hm_post.2.2 a hmp).2
      have hm_R_f : h_R.Matches (subroutineHookExit prog s0 sf').mem := by
        rw [subroutineHookExit_mem]
        exact Heap.Matches.restoreCodeMem_of_eq_none hm_R' hR_none
          (fun a _ hmp => hm_R.2.2 a hmp)
      have h_combined :
          (subroutineHookExit prog s0 sf').mem ⊨
            (memRegion prog.base prog.code.length ∗ innerSpec.post x s0' sf') ∗ R := by
        rw [sepConj_assoc]
        refine SepProp.satisfies_iff.2
          ⟨(regionHeap prog.base prog.code.length m_w).union (hp_post.union h_R),
          SepProp.holds_sepConj_iff.2
            ⟨regionHeap prog.base prog.code.length m_w, hp_post.union h_R, hd_code_postR, rfl,
            holds_memRegion_iff.2 ⟨m_w, rfl⟩,
            SepProp.holds_sepConj_iff.2 ⟨hp_post, h_R, hd_post_R, rfl, hpost_in, hR_sat⟩⟩, ?_⟩
        exact Heap.Matches.union hm_code_f (Heap.Matches.union hm_post_f hm_R_f)
      exact Satisfies.mono (sepConj_mono_left (h_post x s0 sf')) h_combined
  · exact False.elim (h_no_panic x R_sing s0 sf' hpan hq)
  · exact False.elim (h_no_exit x code R_sing s0 sf' hex hq)
  · refine ⟨keepsFrozen_restoreCodeMem h_steps.keepsFrozen, ?_, Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))⟩
    · rw [subroutineHookExit_symtab, h_steps.symtab_eq, subroutineHookEntry_symtab]
    · simp [subroutineHookExit, hoom, State.setMem, State.writeReg64]
    · exact h_oom x R h_R s0 sf' hR_sat
        (fun a ha => ⟨hR_none a ha, fun hmp => hm_R.2.2 a hmp⟩) hoom hq

/-- Lift a memory-preserving subroutine execution (`sf'.mem = s0'.mem`) to
    `HookOk (subroutineHook prog entry_pc) spec` without requiring
    `memRegion prog.base prog.code.length` in `spec.pre`. -/
theorem subroutineHook_ok_readOnly {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α}
    (h_al : prog.base.toNat % 4 = 0)
    (h_ext1 : prog.externAt? (prog.base + 1#64) = none)
    (h_exec : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      s0.spAligned = true →
      let s0' := subroutineHookEntry prog entry_pc s0
      ∃ sf', Steps prog s0' sf' ∧
        Returned s0' sf' ∧
        CallingConventionPreserved s0' sf' ∧
        sf'.mem = s0'.mem ∧
        (s0.mem ⊨ spec.post x s0 (subroutineHookExit prog s0 sf') ∗ R)) :
    HookOk (subroutineHook prog entry_pc) spec := by
  intro x R s0 hrun hpre hsp
  obtain ⟨sf', h_steps, hret, hcc, hmem_eq, hpost⟩ := h_exec x R s0 hrun hpre hsp
  have hmem_exit : (subroutineHookExit prog s0 sf').mem = s0.mem := by
    simp [subroutineHookExit_mem, hmem_eq, subroutineHookEntry, State.setMem]
  have hout' : SubroutineOutcome
      { pre := fun (_ : Unit) _ => emp, post := fun _ _ _ => emp } () emp
      (subroutineHookEntry prog entry_pc s0) sf' :=
    Or.inl ⟨hret, hcc, by simp⟩
  have hhook_eq : subroutineHook prog entry_pc s0 = subroutineHookExit prog s0 sf' :=
    subroutineHook_eq_of_steps_outcome h_al h_ext1 h_steps hout'
  rw [hhook_eq]
  refine ⟨?_, ?_, Or.inl ⟨subroutineHookExit_returned hret, subroutineHookExit_cc hcc, ?_⟩⟩
  · rw [hmem_exit]; exact Memory.KeepsFrozen.refl _
  · rw [subroutineHookExit_symtab, h_steps.symtab_eq, subroutineHookEntry_symtab]
  · rw [hmem_exit]; exact hpost

/-- Introduce any read-only block `P_ro` (`IsBlockRO P_ro base len Φ`) into `m ⊨ P` whenever
    `Φ m` holds and `[base, base + len)` is mapped read-execute (`m.RX base len`), with no
    `DisjointRegions` or `SepProp.NoRO` premise required. -/
theorem IsBlockRO.intro_of_rx {P_ro P : SepProp} {base : BitVec 64} {len : Nat}
    {Φ : Memory → Prop} (hblk : IsBlockRO P_ro base len Φ)
    {m : Memory} (hrx : m.RX base len) (hΦ : Φ m) (hP : m ⊨ P) :
    m ⊨ P_ro ∗ P := by
  obtain ⟨hp, hP_hp, hm⟩ := SepProp.satisfies_iff.1 hP
  have hperm_r : m.Readable base len := by
    intro a ha
    have ⟨hrx_a, hlf_a⟩ := hrx a ha
    exact ⟨by rw [hrx_a]; rfl, hlf_a⟩
  have hm_ro : (regionHeapRO base len m).Matches m :=
    IsBlockRO.regionHeapRO_matches base len m hperm_r
  have hdisj : (regionHeapRO base len m).Disjoint hp := by
    refine Heap.Disjoint.of_phys_left rfl rfl fun a => ?_
    by_cases ha : InRegion base len a
    · cases hpa : hp.phys a with
      | none => exact Or.inr (Or.inl rfl)
      | some c =>
        cases c with
        | rw b =>
          have hrw := (hm.1 a (.rw b) hpa).2.1
          have hrx_a := (hrx a ha).1
          rw [hrw] at hrx_a
          cases hrx_a
        | ro b =>
          have hb := (hm.1 a (.ro b) hpa).1
          subst hb
          exact Or.inr (Or.inr ⟨m.read8 a, by simp [regionHeapRO, ha], rfl⟩)
        | protNone b =>
          have hpn := (hm.1 a (.protNone b) hpa).2.1
          have hrx_a := (hrx a ha).1
          rw [hpn] at hrx_a
          cases hrx_a
        | lazy =>
          have hrw := hm.1 a .lazy hpa
          have hrx_a := (hrx a ha).1
          rw [hrw] at hrx_a
          cases hrx_a
        | protNoneLazy =>
          have hpn := hm.1 a .protNoneLazy hpa
          have hrx_a := (hrx a ha).1
          rw [hpn] at hrx_a
          cases hrx_a
    · exact Or.inl (by simp [regionHeapRO, ha])
  exact SepProp.satisfies_iff.2 ⟨(regionHeapRO base len m).union hp,
    SepProp.holds_sepConj_iff.2
      ⟨regionHeapRO base len m, hp, hdisj, rfl, (hblk.iff _).mpr ⟨m, hΦ, rfl⟩, hP_hp⟩,
    Heap.Matches.union hm_ro hm⟩

end UnsealSepLogic

theorem subroutineHookEntry_mem_of_codeLoaded {prog : Program} {entry_pc : BitVec 64} {s0 : State}
    (hL : prog.CodeLoaded s0.mem) :
    (subroutineHookEntry prog entry_pc s0).mem = s0.mem := by
  simp [subroutineHookEntry, State.setMem, loadCodeMem_eq_of_codeLoaded hL]

theorem subroutineHookExit_mem_of_codeLoaded {prog : Program} {s0 sf' : State}
    (hL0 : prog.CodeLoaded s0.mem) (hLf : prog.CodeLoaded sf'.mem) :
    (subroutineHookExit prog s0 sf').mem = sf'.mem := by
  simp [subroutineHookExit_mem, restoreCodeMem_eq_of_codeLoaded hL0 hLf]

/-- Lift `subroutine_ok prog entry_pc innerSpec` to `HookOk (subroutineHook prog entry_pc) spec`
    when `prog.CodeLoaded` holds at hook entry, without requiring `memRegion prog.base prog.code.length`
    or `SepProp.NoRO`. -/
theorem subroutineHook_ok_of_codeLoaded {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {innerSpec spec : Spec α}
    (h_ext1 : prog.externAt? (prog.base + 1#64) = none)
    (h_sub : subroutine_ok prog entry_pc innerSpec)
    (h_pre : ∀ x s0,
      spec.pre x s0 ⊢
        ⌜prog.CodeLoaded s0.mem⌝ ∗
        innerSpec.pre x (subroutineHookEntry prog entry_pc s0))
    (h_post : ∀ x s0 sf',
      prog.CodeLoaded s0.mem →
      (⌜prog.CodeLoaded sf'.mem⌝ ∗
        innerSpec.post x (subroutineHookEntry prog entry_pc s0) sf') ⊢
        spec.post x s0 (subroutineHookExit prog s0 sf'))
    (h_no_panic : ∀ x R' s0 sf', sf'.status = .Panicked →
      ¬(sf'.mem ⊨ innerSpec.onPanic x (subroutineHookEntry prog entry_pc s0) sf' ∗ R') := by
      intro _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ x code R' s0 sf', sf'.status = .Exited code →
      ¬(sf'.mem ⊨ innerSpec.onExit x code (subroutineHookEntry prog entry_pc s0) sf' ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ x s0 sf',
      prog.CodeLoaded s0.mem →
      prog.CodeLoaded sf'.mem →
      sf'.status = .OutOfMemory →
      innerSpec.onOom x (subroutineHookEntry prog entry_pc s0) sf' ⊢
        spec.onOom x s0 (subroutineHookExit prog s0 sf') := by
      intro _ _ _ _ _ _
      try simp only [Spec.codeLoadedSubroutineHook, Spec.allowOom]
      exact Entails.refl _) :
    HookOk (subroutineHook prog entry_pc) spec := by
  intro x R s0 hrun hpre_sat hsp
  have hpre_framed : s0.mem ⊨
      (⌜prog.CodeLoaded s0.mem⌝ ∗
        innerSpec.pre x (subroutineHookEntry prog entry_pc s0)) ∗ R :=
    Satisfies.mono (sepConj_mono_left (h_pre x s0)) hpre_sat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_framed
  rcases hpre_framed with ⟨hL0, hin_pre⟩
  let s0' := subroutineHookEntry prog entry_pc s0
  have hs0'_mem : s0'.mem = s0.mem := subroutineHookEntry_mem_of_codeLoaded hL0
  have hs0'_pre : s0'.mem ⊨ innerSpec.pre x s0' ∗ R := by
    rw [hs0'_mem]; exact hin_pre
  have hL0' : prog.CodeLoaded s0'.mem := by
    rw [hs0'_mem]; exact hL0
  have hs0'_pc : s0'.pc = entry_pc := rfl
  have hs0'_run : s0'.status = .Running := hrun
  have hs0'_sp : s0'.spAligned = true := by
    simpa [s0', subroutineHookEntry, State.spAligned, State.setMem, State.setPC,
      State.writeReg64] using hsp
  obtain ⟨sf', h_steps, hout⟩ := reaches_outcome_iff.1 (subroutine_ok_iff.1 h_sub x R s0' hs0'_pc hs0'_run hs0'_pre hs0'_sp) hL0'
  have hLf : prog.CodeLoaded sf'.mem := h_steps.codeLoaded hL0'
  have hsf_mem : (subroutineHookExit prog s0 sf').mem = sf'.mem :=
    subroutineHookExit_mem_of_codeLoaded hL0 hLf
  have hhook_eq : subroutineHook prog entry_pc s0 = subroutineHookExit prog s0 sf' :=
    subroutineHook_eq_of_steps_outcome hL0.aligned h_ext1 h_steps hout
  rw [hhook_eq]
  have hkf : s0.mem.KeepsFrozen (subroutineHookExit prog s0 sf').mem := by
    rw [← hs0'_mem, hsf_mem]
    exact h_steps.keepsFrozen
  have hsym : (subroutineHookExit prog s0 sf').symtab = s0.symtab := by
    rw [subroutineHookExit_symtab, h_steps.symtab_eq, subroutineHookEntry_symtab]
  rcases hout with ⟨hret, hcc, hpost_sat⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine ⟨hkf, hsym, Or.inl ⟨subroutineHookExit_returned hret, subroutineHookExit_cc hcc, ?_⟩⟩
    rw [hsf_mem]
    have h_comb : sf'.mem ⊨ (⌜prog.CodeLoaded sf'.mem⌝ ∗ innerSpec.post x s0' sf') ∗ R := by
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hLf, hpost_sat⟩
    exact Satisfies.mono (sepConj_mono_left (h_post x s0 sf' hL0)) h_comb
  · exact False.elim (h_no_panic x R s0 sf' hpan hq)
  · exact False.elim (h_no_exit x code R s0 sf' hex hq)
  · refine ⟨hkf, hsym, Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))⟩
    · simp [subroutineHookExit, hoom, State.setMem, State.writeReg64]
    · rw [hsf_mem]
      exact Satisfies.mono (sepConj_mono_left (h_oom x s0 sf' hL0 hLf hoom)) hq

theorem subroutineHook_ok_codeLoadedSubroutineHook {S β : Type} [ToBaseSpec S β]
    {prog : Program} (name : String) {spec : S}
    (h_ext1 : prog.externAt? (prog.base + 1#64) = none)
    (h_sub : prog.subroutineOk name spec)
    (h_no_panic : ∀ x R' s0 sf', sf'.status = .Panicked →
      ¬(sf'.mem ⊨ (ToBaseSpec.toSpec spec prog.base).onPanic x
        (subroutineHookEntry prog (prog.fnAddr name) s0) sf' ∗ R') := by
      intro _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ x code R' s0 sf', sf'.status = .Exited code →
      ¬(sf'.mem ⊨ (ToBaseSpec.toSpec spec prog.base).onExit x code
        (subroutineHookEntry prog (prog.fnAddr name) s0) sf' ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ x s0 sf',
      prog.CodeLoaded s0.mem →
      prog.CodeLoaded sf'.mem →
      sf'.status = .OutOfMemory →
      (ToBaseSpec.toSpec spec prog.base).onOom x
        (subroutineHookEntry prog (prog.fnAddr name) s0) sf' ⊢
        (Spec.codeLoadedSubroutineHook prog name spec).onOom x s0
          (subroutineHookExit prog s0 sf') := by
      intro _ _ _ _ _ _
      try simp only [Spec.codeLoadedSubroutineHook, Spec.allowOom]
      exact Entails.refl _) :
    HookOk (subroutineHook prog (prog.fnAddr name))
      (Spec.codeLoadedSubroutineHook prog name spec) := by
  refine subroutineHook_ok_of_codeLoaded h_ext1 h_sub
    (fun _ _ => Entails.refl _)
    (fun _ s0 sf' hL0 => ?_)
    h_no_panic h_no_exit h_oom
  refine Entails.pure_left fun hLf => ?_
  have hLf_exit : prog.CodeLoaded (subroutineHookExit prog s0 sf').mem := by
    rwa [subroutineHookExit_mem_of_codeLoaded hL0 hLf]
  exact Entails.sepExists_right sf' (Entails.pure_right ⟨rfl, hLf_exit⟩ (Entails.refl _))

/-- Split a `SepWP` proof at an intermediate PC `mid`, re-establishing `calleeProg.CodeLoaded sm.mem`
    at `mid` across any preceding instructions (including memory stores). -/
theorem SepWP.seq_codeLoaded {prog calleeProg : Program} {mid target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hL : calleeProg.CodeLoaded s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      calleeProg.CodeLoaded sm.mem →
      SepWP prog target_pc sm Pm post oom) oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm hLp
  rcases h R hm hLp with ⟨sm, hst1, ⟨_, _, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hst2, hout⟩ :=
      hcont (hL.of_keepsFrozen hst1.keepsFrozen) R hmm (hst1.codeLoaded hLp)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact ⟨sm, hst1, Or.inr hoom⟩

/-- Postcondition weakening for `SepWP` that supplies `calleeProg.CodeLoaded sf.mem` at `target_pc`
    from `calleeProg.CodeLoaded s.mem` at start state `s`. -/
theorem SepWP.mono_codeLoaded {prog calleeProg : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {post post' : State → SepProp → Prop} {oom : State → SepProp}
    (hL : calleeProg.CodeLoaded s.mem)
    (h : SepWP prog target_pc s P post oom)
    (himp : ∀ sf Pf, sf.pc = target_pc → sf.status = .Running →
      calleeProg.CodeLoaded sf.mem → post sf Pf → post' sf Pf) :
    SepWP prog target_pc s P post' oom := by
  intro R hm hLp
  rcases h R hm hLp with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hp⟩ | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf,
      himp sf Pf hpc hrun (hL.of_keepsFrozen hsteps.keepsFrozen) hp⟩⟩
  · exact ⟨sf, hsteps, Or.inr hoom⟩

/-! ## Linux `SYS_MMAP` Step Rules -/

private theorem readBytes_mapZero_aux {m : Memory} {base : BitVec 64} {len : Nat}
    (hmap : m.canMap base len = true) (hlen : len ≤ 2 ^ 64) :
    ∀ (k off : Nat), off + k ≤ len →
      (m.mapZero base len).readBytes (base + BitVec.ofNat 64 off) k = List.replicate k 0#8
  | 0, _, _ => rfl
  | k + 1, off, hle => by
    have ha : InRegion base len (base + BitVec.ofNat 64 off) := by
      simp only [InRegion]
      have hsub : base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off := by
        rw [BitVec.add_comm, BitVec.add_sub_cancel]
      rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hr8 := m.read8_mapZero_of_canMap hmap ha
    have hstep : base + BitVec.ofNat 64 off + 1#64 = base + BitVec.ofNat 64 (off + 1) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    simp only [Memory.readBytes, List.replicate_succ, hr8, hstep,
      readBytes_mapZero_aux hmap hlen k (off + 1) (by omega)]

/-- Mapping an unmapped region `[base, base + len)` with `Memory.mapZero` (`mmap`) adds a
    zero-initialized byte slice `base ↦ₛ List.replicate len 0#8` alongside `memMapped base len`
    and any existing assertion `P`. -/
theorem Satisfies.mapZero_bytes_mapped {P : SepProp} {m : Memory} (h : m ⊨ P)
    {base : BitVec 64} {len : Nat} (hmap : m.canMap base len = true) (hlen : len ≤ 2 ^ 64) :
    m.mapZero base len ⊨ (base ↦ₛ List.replicate len 0#8) ∗ memMapped base len ∗ P := by
  have hm := Satisfies.mapZero_mapped h hmap
  have hblk := IsBlock.pointsToBytes_len (a := base) (bs := List.replicate len 0#8)
    List.length_replicate
  refine (IsBlock.memRegion base len).update hblk (Nat.le_refl _) hm
    (AgreesOutside.rfl' _ base len) ⟨by simp [hlen], ?_⟩
  simpa using readBytes_mapZero_aux hmap hlen len 0 (by omega)

/-- Mapping an unmapped region `[base, base + len)` with `Memory.mapZero` (`mmap`) adds a
    zero-initialized byte slice `base ↦ₛ List.replicate len 0#8` alongside any existing assertion `P`. -/
theorem Satisfies.mapZero_bytes {P : SepProp} {m : Memory} (h : m ⊨ P)
    {base : BitVec 64} {len : Nat} (hmap : m.canMap base len = true) (hlen : len ≤ 2 ^ 64) :
    m.mapZero base len ⊨ (base ↦ₛ List.replicate len 0#8) ∗ P := by
  have hm := Satisfies.mapZero h hmap
  have hblk := IsBlock.pointsToBytes_len (a := base) (bs := List.replicate len 0#8)
    List.length_replicate
  refine (IsBlock.memRegion base len).update hblk (Nat.le_refl _) hm
    (AgreesOutside.rfl' _ base len) ⟨by simp [hlen], ?_⟩
  simpa using readBytes_mapZero_aux hmap hlen len 0 (by omega)

@[simp, arm64_norm, wp_norm]
theorem _root_.Arm64.State.spAligned_nextOracle (s : State) :
    s.nextOracle.spAligned = s.spAligned := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem _root_.Arm64.State.spAligned_stepExclOracle (s : State) :
    s.stepExclOracle.spAligned = s.spAligned := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem _root_.Arm64.State.spAligned_stepExclLoop (s : State) :
    s.stepExclLoop.spAligned = s.spAligned := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem _root_.Arm64.checkAddrSPAligned_nextOracle (s : State) (am : AddrMode) :
    checkAddrSPAligned s.nextOracle am = checkAddrSPAligned s am := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem _root_.Arm64.checkAddrSPAligned_stepExclOracle (s : State) (am : AddrMode) :
    checkAddrSPAligned s.stepExclOracle am = checkAddrSPAligned s am := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem _root_.Arm64.checkAddrSPAligned_stepExclLoop (s : State) (am : AddrMode) :
    checkAddrSPAligned s.stepExclLoop am = checkAddrSPAligned s am := by
  cases s; rfl

/-- Step rule for Linux AArch64 anonymous `SYS_MMAP` (`svc #0` with `X8 = 222`, `X2 = 3`,
    `X3 ∈ {0x22, 0x20022}`, `X5 = 0`, `0 < len`) inside `SepWP` that also produces the
    virtual-address mapping reservation token `memMapped mb (pageAlignUp len)`: either the kernel
    oracle maps a fresh page-aligned zero-initialized region
    `(mb ↦ₛ List.replicate (pageAlignUp len) 0#8) ∗ memMapped mb (pageAlignUp len)` with `mb ≠ 0`,
    `4096 ∣ mb.toNat`, and `mb.toNat + pageAlignUp len ≤ 2^48`, or `execMmap` transitions to
    `.OutOfMemory`. -/
theorem SepWP.step_svc_mmap_anon_mapped {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {len : Nat}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64)
    (hprot : s.readReg64 .x2 = 3#64)
    (hflags : s.readReg64 .x3 = 0x22#64 ∨ s.readReg64 .x3 = 0x20022#64)
    (hoff : s.readReg64 .x5 = 0#64)
    (hlen_eq : (s.readReg64 .x1).toNat = len)
    (hlen0 : 0 < len)
    (hok : ∀ (mb : BitVec 64) (m' : Memory),
      mb ≠ 0#64 → 4096 ∣ mb.toNat → mb.toNat + pageAlignUp len ≤ 2 ^ 48 →
      SepWP prog target_pc
        ((((s.setPhysMemAvail (s.physMemAvail - pageAlignUp len)).nextOracle.writeReg64 .x0 mb).setPC
          (pc + 4#64)).setMem m')
        ((mb ↦ₛ List.replicate (pageAlignUp len) 0#8) ∗ memMapped mb (pageAlignUp len) ∗ P) post oom)
    (hoom : ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R) := by
      intro _ hm; (try simp only [wp_unfold, Spec.allowOom] at hm ⊢); first | exact satisfies_true_sepConj hm | exact satisfies_true_sepConj_frame hm)
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s := by simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom := by
  subst hlen_eq
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.system false 0#16) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  rw [hsvc]
  have hlen_ne : s.readReg64 .x1 ≠ 0#64 := by
    intro h; rw [h] at hlen0; contradiction
  cases hsan : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) with
  | some mb =>
    by_cases hphys : pageAlignUp (s.readReg64 .x1).toNat ≤ s.physMemAvail
    · obtain ⟨hne, hal, hfit, hmap⟩ := sanitizeMmapAddr_spec hsan
      unfold USER_VA_LIMIT at hfit
      rw [execMmap_anon_sanitized_ok s hprot hflags hoff hlen_ne hsan hphys]
      have hdvd : 4096 ∣ mb.toNat := by
        unfold PAGE_SIZE at hal; exact Nat.dvd_of_mod_eq_zero hal
      have hm' := Satisfies.mapZero_bytes_mapped hm hmap (by omega)
      have hm'' : (s.mem.mapZero mb (pageAlignUp (s.readReg64 .x1).toNat)) ⊨
          ((mb ↦ₛ List.replicate (pageAlignUp (s.readReg64 .x1).toNat) 0#8) ∗
            memMapped mb (pageAlignUp (s.readReg64 .x1).toNat) ∗ P) ∗ R := by
        simpa [sepConj_assoc] using hm'
      have hst :
          ((((s.setMem (s.mem.mapZero mb (pageAlignUp (s.readReg64 .x1).toNat))).setPhysMemAvail
              (s.physMemAvail - pageAlignUp (s.readReg64 .x1).toNat)).nextOracle).writeReg64
            .x0 mb).advancePC =
          ((((s.setPhysMemAvail (s.physMemAvail - pageAlignUp (s.readReg64 .x1).toNat)).nextOracle.writeReg64
            .x0 mb).setPC (pc + 4#64)).setMem
            (s.mem.mapZero mb (pageAlignUp (s.readReg64 .x1).toNat))) := by
        cases s; simp [State.setMem, State.setPhysMemAvail, State.nextOracle, State.writeReg64,
          State.advancePC, State.setPC] at hpc ⊢
        exact hpc
      rw [hst]
      exact hok mb _ hne hdvd hfit R hm''
    · rw [execMmap_anon_sanitized_oom s hprot hflags hoff hlen_ne hsan hphys]
      exact reaches_pc_oom rfl (by simpa [State.setStatus] using hoom R hm)
  | none =>
    rw [execMmap_anon_oom s hprot hflags hoff hlen_ne hsan]
    exact reaches_pc_oom rfl (by simpa [State.setStatus] using hoom R hm)

/-- Step rule for Linux AArch64 anonymous `SYS_MMAP` (`svc #0` with `X8 = 222`, `X2 = 3`,
    `X3 ∈ {0x22, 0x20022}`, `X5 = 0`, `0 < len`) inside `SepWP`: either the kernel oracle maps a
    fresh page-aligned zero-initialized region `mb ↦ₛ List.replicate (pageAlignUp len) 0#8` with
    `mb ≠ 0`, `4096 ∣ mb.toNat`, and `mb.toNat + pageAlignUp len ≤ 2^48`, or `execMmap` transitions
    to `.OutOfMemory`. -/
theorem SepWP.step_svc_mmap_anon {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {len : Nat}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64)
    (hprot : s.readReg64 .x2 = 3#64)
    (hflags : s.readReg64 .x3 = 0x22#64 ∨ s.readReg64 .x3 = 0x20022#64)
    (hoff : s.readReg64 .x5 = 0#64)
    (hlen_eq : (s.readReg64 .x1).toNat = len)
    (hlen0 : 0 < len)
    (hok : ∀ (mb : BitVec 64) (m' : Memory),
      mb ≠ 0#64 → 4096 ∣ mb.toNat → mb.toNat + pageAlignUp len ≤ 2 ^ 48 →
      SepWP prog target_pc
        ((((s.setPhysMemAvail (s.physMemAvail - pageAlignUp len)).nextOracle.writeReg64 .x0 mb).setPC
          (pc + 4#64)).setMem m')
        ((mb ↦ₛ List.replicate (pageAlignUp len) 0#8) ∗ P) post oom)
    (hoom : ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R) := by
      intro _ hm; (try simp only [wp_unfold, Spec.allowOom] at hm ⊢); first | exact satisfies_true_sepConj hm | exact satisfies_true_sepConj_frame hm)
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s := by simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom := by
  subst hlen_eq
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.system false 0#16) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  rw [hsvc]
  have hlen_ne : s.readReg64 .x1 ≠ 0#64 := by
    intro h; rw [h] at hlen0; contradiction
  cases hsan : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) with
  | some mb =>
    by_cases hphys : pageAlignUp (s.readReg64 .x1).toNat ≤ s.physMemAvail
    · obtain ⟨hne, hal, hfit, hmap⟩ := sanitizeMmapAddr_spec hsan
      unfold USER_VA_LIMIT at hfit
      rw [execMmap_anon_sanitized_ok s hprot hflags hoff hlen_ne hsan hphys]
      have hdvd : 4096 ∣ mb.toNat := by
        unfold PAGE_SIZE at hal; exact Nat.dvd_of_mod_eq_zero hal
      have hm' := Satisfies.mapZero_bytes hm hmap (by omega)
      rw [← sepConj_assoc] at hm'
      have hst :
          ((((s.setMem (s.mem.mapZero mb (pageAlignUp (s.readReg64 .x1).toNat))).setPhysMemAvail
              (s.physMemAvail - pageAlignUp (s.readReg64 .x1).toNat)).nextOracle).writeReg64
            .x0 mb).advancePC =
          ((((s.setPhysMemAvail (s.physMemAvail - pageAlignUp (s.readReg64 .x1).toNat)).nextOracle.writeReg64
            .x0 mb).setPC (pc + 4#64)).setMem
            (s.mem.mapZero mb (pageAlignUp (s.readReg64 .x1).toNat))) := by
        cases s; simp [State.setMem, State.setPhysMemAvail, State.nextOracle, State.writeReg64,
          State.advancePC, State.setPC] at hpc ⊢
        exact hpc
      rw [hst]
      exact hok mb _ hne hdvd hfit R hm'
    · rw [execMmap_anon_sanitized_oom s hprot hflags hoff hlen_ne hsan hphys]
      exact reaches_pc_oom rfl (by simpa [State.setStatus] using hoom R hm)
  | none =>
    rw [execMmap_anon_oom s hprot hflags hoff hlen_ne hsan]
    exact reaches_pc_oom rfl (by simpa [State.setStatus] using hoom R hm)

/-- Step rule for Linux AArch64 `SYS_MMAP` (`svc #0` with `X8 = 222`, `X2 = 3`, `X3 = 0x22`, `X5 = 0`)
    inside `SepWP` that produces `memMapped mb len` and `MMAP_MIN_ADDR ≤ mb.toNat`. -/
theorem SepWP.step_svc_mmap_mapped_min {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {len : Nat}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64)
    (hprot : s.readReg64 .x2 = 3#64)
    (hflags : s.readReg64 .x3 = 0x22#64)
    (hoff : s.readReg64 .x5 = 0#64)
    (hlen_eq : (s.readReg64 .x1).toNat = len)
    (hlen0 : 0 < len)
    (hlen4096 : 4096 ∣ len)
    (hok : ∀ (mb : BitVec 64) (m' : Memory),
      MMAP_MIN_ADDR ≤ mb.toNat → mb ≠ 0#64 → 4096 ∣ mb.toNat → mb.toNat + len ≤ 2 ^ 48 →
      SepWP prog target_pc
        ((((s.setPhysMemAvail (s.physMemAvail - len)).nextOracle.writeReg64 .x0 mb).setPC
          (pc + 4#64)).setMem m')
        ((mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗ P) post oom)
    (hoom : ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R) := by
      intro _ hm; (try simp only [wp_unfold, Spec.allowOom] at hm ⊢); first | exact satisfies_true_sepConj hm | exact satisfies_true_sepConj_frame hm)
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s := by simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom := by
  subst hlen_eq
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.system false 0#16) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  rw [hsvc]
  have hlen_ne : s.readReg64 .x1 ≠ 0#64 := by
    intro h; rw [h] at hlen0; contradiction
  have halign : pageAlignUp (s.readReg64 .x1).toNat = (s.readReg64 .x1).toNat :=
    pageAlignUp_of_dvd hlen4096
  cases hsan : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) with
  | some mb =>
    by_cases hphys : pageAlignUp (s.readReg64 .x1).toNat ≤ s.physMemAvail
    · have hmin := sanitizeMmapAddr_min hsan
      obtain ⟨hne, hal, hfit, hmap⟩ := sanitizeMmapAddr_spec hsan
      rw [execMmap_sanitized_ok s hprot hflags hoff hlen_ne hsan hphys, halign]
      rw [halign] at hfit hmap
      have hdvd : 4096 ∣ mb.toNat := by
        unfold PAGE_SIZE at hal; exact Nat.dvd_of_mod_eq_zero hal
      have hm' := Satisfies.mapZero_bytes_mapped hm hmap (by omega)
      have hm'' : (s.mem.mapZero mb (s.readReg64 .x1).toNat) ⊨
          ((mb ↦ₛ List.replicate (s.readReg64 .x1).toNat 0#8) ∗
            memMapped mb (s.readReg64 .x1).toNat ∗ P) ∗ R := by
        simpa [sepConj_assoc] using hm'
      have hst :
          ((((s.setMem (s.mem.mapZero mb (s.readReg64 .x1).toNat)).setPhysMemAvail
              (s.physMemAvail - (s.readReg64 .x1).toNat)).nextOracle).writeReg64
            .x0 mb).advancePC =
          ((((s.setPhysMemAvail (s.physMemAvail - (s.readReg64 .x1).toNat)).nextOracle.writeReg64
            .x0 mb).setPC (pc + 4#64)).setMem
            (s.mem.mapZero mb (s.readReg64 .x1).toNat)) := by
        cases s; simp [State.setMem, State.setPhysMemAvail, State.nextOracle, State.writeReg64,
          State.advancePC, State.setPC] at hpc ⊢
        exact hpc
      rw [hst]
      exact hok mb _ hmin hne hdvd hfit R hm''
    · rw [execMmap_sanitized_oom s hprot hflags hoff hlen_ne hsan hphys]
      exact reaches_pc_oom rfl (by simpa [State.setStatus] using hoom R hm)
  | none =>
    rw [execMmap_oom s hprot hflags hoff hlen_ne hsan]
    exact reaches_pc_oom rfl (by simpa [State.setStatus] using hoom R hm)

/-- Step rule for Linux AArch64 `SYS_MMAP` (`svc #0` with `X8 = 222`, `X2 = 3`, `X3 = 0x22`, `X5 = 0`)
    inside `SepWP` that also produces the virtual-address mapping reservation token `memMapped mb len`:
    either the kernel oracle maps a fresh page-aligned zero-initialized region
    `(mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len` with `mb ≠ 0`, `4096 ∣ mb.toNat`, and
    `mb.toNat + len ≤ 2^48`, or `execMmap` transitions to `.OutOfMemory`. -/
theorem SepWP.step_svc_mmap_mapped {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {len : Nat}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64)
    (hprot : s.readReg64 .x2 = 3#64)
    (hflags : s.readReg64 .x3 = 0x22#64)
    (hoff : s.readReg64 .x5 = 0#64)
    (hlen_eq : (s.readReg64 .x1).toNat = len)
    (hlen0 : 0 < len)
    (hlen4096 : 4096 ∣ len)
    (hok : ∀ (mb : BitVec 64) (m' : Memory),
      mb ≠ 0#64 → 4096 ∣ mb.toNat → mb.toNat + len ≤ 2 ^ 48 →
      SepWP prog target_pc
        ((((s.setPhysMemAvail (s.physMemAvail - len)).nextOracle.writeReg64 .x0 mb).setPC
          (pc + 4#64)).setMem m')
        ((mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗ P) post oom)
    (hoom : ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R) := by
      intro _ hm; (try simp only [wp_unfold, Spec.allowOom] at hm ⊢); first | exact satisfies_true_sepConj hm | exact satisfies_true_sepConj_frame hm)
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s := by simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_svc_mmap_mapped_min hpc hrun hfetch hx8 hprot hflags hoff hlen_eq hlen0 hlen4096
    (fun mb m' _ hne hdvd hfit => hok mb m' hne hdvd hfit) hoom hsvc

/-- Step rule for Linux AArch64 `SYS_MMAP` (`svc #0` with `X8 = 222`, `X2 = 3`, `X3 = 0x22`, `X5 = 0`)
    inside `SepWP`: either the kernel oracle maps a fresh page-aligned zero-initialized region
    `mb ↦ₛ List.replicate len 0#8` with `mb ≠ 0`, `4096 ∣ mb.toNat`, and `mb.toNat + len ≤ 2^48`,
    or `execMmap` transitions to `.OutOfMemory` (which satisfies `reaches_pc` automatically). -/
theorem SepWP.step_svc_mmap {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {len : Nat}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64)
    (hprot : s.readReg64 .x2 = 3#64)
    (hflags : s.readReg64 .x3 = 0x22#64)
    (hoff : s.readReg64 .x5 = 0#64)
    (hlen_eq : (s.readReg64 .x1).toNat = len)
    (hlen0 : 0 < len)
    (hlen4096 : 4096 ∣ len)
    (hok : ∀ (mb : BitVec 64) (m' : Memory),
      mb ≠ 0#64 → 4096 ∣ mb.toNat → mb.toNat + len ≤ 2 ^ 48 →
      SepWP prog target_pc
        ((((s.setPhysMemAvail (s.physMemAvail - len)).nextOracle.writeReg64 .x0 mb).setPC
          (pc + 4#64)).setMem m')
        ((mb ↦ₛ List.replicate len 0#8) ∗ P) post oom)
    (hoom : ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R) := by
      intro _ hm; (try simp only [wp_unfold, Spec.allowOom] at hm ⊢); first | exact satisfies_true_sepConj hm | exact satisfies_true_sepConj_frame hm)
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s := by simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.step_svc_mmap_anon hpc hrun hfetch hx8 hprot (Or.inl hflags) hoff hlen_eq
    hlen0 ?_ hoom hsvc
  intro mb m' hne hdvd hfit
  rw [pageAlignUp_of_dvd hlen4096] at hfit ⊢
  exact hok mb m' hne hdvd hfit

/-- Step rule for a Linux AArch64 `MAP_FIXED` `PROT_NONE` `SYS_MMAP` (`svc #0` with `X8 = 222`,
    `X0 = addr`, `X1 = len`, `X2 = PROT_NONE = 0`, `X3 = MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED = 0x32`,
    `X5 = 0`) inside `SepWP`, as an allocator issues for a guard page: an owned, page-aligned
    region `memRegion addr len` (`addr ≥ MMAP_MIN_ADDR`, `addr + len ≤ 2^48`, `4096 ∣ len`) is
    replaced by inaccessible pages and given up, `X0 = addr`, and the oracle is not consulted (the
    call cannot fail). -/
theorem SepWP.step_svc_mmap_fixed_protNone {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc addr : BitVec 64} {len : Nat}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64)
    (haddr : s.readReg64 .x0 = addr)
    (hprot : s.readReg64 .x2 = 0#64)
    (hflags : s.readReg64 .x3 = 0x32#64)
    (hoff : s.readReg64 .x5 = 0#64)
    (hlen_eq : (s.readReg64 .x1).toNat = len)
    (hlen0 : 0 < len)
    (hlen4096 : 4096 ∣ len)
    (hal : 4096 ∣ addr.toNat)
    (hmin : 65536 ≤ addr.toNat)
    (hfit : addr.toNat + len ≤ 2 ^ 48)
    (hok : ∀ m' : Memory,
      SepWP prog target_pc
        ((((s.setPhysMemAvail (s.physMemAvail + s.mem.countRw addr len)).writeReg64
          .x0 addr).setPC (pc + 4#64)).setMem m')
        P post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execMmap s := by simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s (memRegion addr len ∗ P) post oom := by
  let _ := hx8
  subst hlen_eq haddr
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.system false 0#16) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  rw [hsvc]
  have hlen_ne : s.readReg64 .x1 ≠ 0#64 := by
    intro h; rw [h] at hlen0; contradiction
  have halign : pageAlignUp (s.readReg64 .x1).toNat = (s.readReg64 .x1).toNat :=
    pageAlignUp_of_dvd hlen4096
  have hm' : s.mem ⊨ memRegion (s.readReg64 .x0) (s.readReg64 .x1).toNat ∗ (P ∗ R) := by
    rw [← sepConj_assoc]; exact hm
  have hrw : s.mem.RW (s.readReg64 .x0) (s.readReg64 .x1).toNat :=
    (IsBlock.memRegion _ _).rw hm'
  have hfrz := hrw.allPerm_not_frozen (by omega)
  rw [execMmap_fixed_protNone_ok s hprot hflags hoff hlen_ne
    (by unfold PAGE_SIZE; exact Nat.mod_eq_zero_of_dvd hal)
    (by unfold MMAP_MIN_ADDR; exact hmin) (by rw [halign]; exact hfit) (by rw [halign]; exact hfrz),
    halign]
  have hst :
      (((s.setMem (((s.mem.unmapNonFrozen (s.readReg64 .x0) (s.readReg64 .x1).toNat).mapZero
          (s.readReg64 .x0) (s.readReg64 .x1).toNat).setPermNonFrozen (s.readReg64 .x0)
          (s.readReg64 .x1).toNat Perm.protNone)).setPhysMemAvail
          (s.physMemAvail + s.mem.countRw (s.readReg64 .x0)
            (s.readReg64 .x1).toNat)).writeReg64 .x0 (s.readReg64 .x0)).advancePC =
      ((((s.setPhysMemAvail (s.physMemAvail + s.mem.countRw (s.readReg64 .x0)
          (s.readReg64 .x1).toNat)).writeReg64 .x0 (s.readReg64 .x0)).setPC (pc + 4#64)).setMem
        (((s.mem.unmapNonFrozen (s.readReg64 .x0) (s.readReg64 .x1).toNat).mapZero
          (s.readReg64 .x0) (s.readReg64 .x1).toNat).setPermNonFrozen (s.readReg64 .x0)
          (s.readReg64 .x1).toNat Perm.protNone)) := by
    cases s; simp [State.setMem, State.setPhysMemAvail, State.writeReg64, State.advancePC,
      State.setPC] at hpc ⊢
    exact hpc
  rw [hst]
  exact hok _ R (Satisfies.mmapFixedProtNone hm')

/-! ## Multi-Block Placed Library Hooks and Read-Only Code -/

private theorem lookupBlockSymAux_lt {name : String} :
    ∀ (idx : Nat) (blocks : List Obj.CodeBlock) {i off : Nat},
      Obj.lookupBlockSymAux name idx blocks = some (i, off) → i < idx + blocks.length
  | _, [], _, _, h => by simp [Obj.lookupBlockSymAux] at h
  | idx, blk :: rest, i, off, h => by
    simp only [Obj.lookupBlockSymAux] at h
    split at h
    · injection h with h; cases h; simp
    · have ih := lookupBlockSymAux_lt (idx + 1) rest h
      simp only [List.length_cons]; omega

theorem lookupBlockSym_lt {name : String} {blocks : List Obj.CodeBlock} {i off : Nat}
    (h : Obj.lookupBlockSym name blocks = some (i, off)) : i < blocks.length := by
  simpa [Obj.lookupBlockSym] using lookupBlockSymAux_lt 0 blocks h

theorem _root_.Arm64.Obj.MultiPlacedLib.blockLib_text_of_lt {lib : Obj.MultiPlacedLib} {i : Nat}
    (hi : i < lib.blocks.length) : (lib.blockLib i).text = lib.blocks[i] := by
  simp [Obj.MultiPlacedLib.blockLib, hi]

@[simp]
theorem _root_.Arm64.Obj.MultiPlacedLib.fnBlockIdx_eq_of_lookup {lib : Obj.MultiPlacedLib}
    {fnName : String} {i off : Nat} (h : Obj.lookupBlockSym fnName lib.blocks = some (i, off)) :
    lib.fnBlockIdx fnName = i := by
  simp [Obj.MultiPlacedLib.fnBlockIdx, h]

theorem _root_.Arm64.Obj.MultiPlacedLib.fnBlockIdx_lt_of_subroutineOk {S α : Type} [ToBaseSpec S α]
    {lib : Obj.MultiPlacedLib} {fnName : String} {spec : Obj.MultiPlacement → S}
    {externs overrides : String → Option (State → State)}
    (h : lib.subroutineOk fnName spec externs overrides) :
    lib.fnBlockIdx fnName < lib.blocks.length := by
  obtain ⟨_, i, off, hlook, _⟩ := h
  rw [lib.fnBlockIdx_eq_of_lookup hlook]
  exact lookupBlockSym_lt hlook

theorem _root_.Arm64.Obj.MultiPlacedLib.subroutineHook_eq_of_lookup {lib : Obj.MultiPlacedLib}
    {mpl : Obj.MultiPlacement} {fnName : String}
    {externs overrides : String → Option (State → State)} {i off : Nat}
    (h : Obj.lookupBlockSym fnName lib.blocks = some (i, off)) :
    lib.subroutineHook mpl fnName externs overrides =
      Arm64.subroutineHook (lib.blockProgram mpl i externs overrides) (lib.fnAddr mpl fnName) := by
  simp [Obj.MultiPlacedLib.subroutineHook, h]

theorem _root_.Arm64.Obj.MultiPlacedLib.subroutineHook_eq_id_of_none {lib : Obj.MultiPlacedLib}
    {mpl : Obj.MultiPlacement} {fnName : String}
    {externs overrides : String → Option (State → State)}
    (h : Obj.lookupBlockSym fnName lib.blocks = none) :
    lib.subroutineHook mpl fnName externs overrides = id := by
  simp [Obj.MultiPlacedLib.subroutineHook, h]

/-- Under `lib.text.Placeable pl` with `externs = fun _ => none`, the return sentinel `pl.base + 1`
    is never a hooked entry point (all block symbols are 4-byte aligned, so offset `1` is absent). -/
theorem _root_.Arm64.Obj.PlacedLib.externAt?_base_add_one_noExterns {lib : Obj.PlacedLib}
    {pl : Obj.Placement} {overrides : String → Option (State → State)} {svc : State → State}
    (hpl : lib.text.Placeable pl) :
    (lib.program pl (fun _ => none) overrides svc).externAt? (pl.base + 1#64) = none := by
  have hoff : (pl.base + 1#64 - pl.base).toNat = 1 := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]; rfl
  simp only [Program.externAt?, Program.hookAtOff?, Obj.PlacedLib.program, hoff,
    Option.or_eq_none_iff, List.findSome?_eq_none_iff]
  refine ⟨fun _ _ => by split <;> rfl, fun s hs => ?_⟩
  have hal := (hpl.symbols_ok s hs).1
  simp [beq_false_of_ne (by omega : s.2 ≠ 1)]

/-- Under `lib.text.Placeable pl` with non-empty code (`0 < lib.text.code.length`), the return
    sentinel `pl.base + 1` is never a hooked entry point for any `externs` or `overrides`: block
    symbols have 4-byte-aligned offsets (`≠ 1`) and extern stubs lie at offset `≥ code.length ≥ 4`. -/
theorem _root_.Arm64.Obj.PlacedLib.externAt?_base_add_one_of_pos {lib : Obj.PlacedLib}
    {pl : Obj.Placement} {externs overrides : String → Option (State → State)} {svc : State → State}
    (hpl : lib.text.Placeable pl) (hpos : 0 < lib.text.code.length) :
    (lib.program pl externs overrides svc).externAt? (pl.base + 1#64) = none := by
  have hoff : (pl.base + 1#64 - pl.base).toNat = 1 := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]; rfl
  have hlen4 : 4 ≤ lib.text.code.length := by have := hpl.len_aligned; omega
  simp only [Program.externAt?, Program.hookAtOff?, Obj.PlacedLib.program, hoff,
    Option.or_eq_none_iff, List.findSome?_eq_none_iff, List.mem_map]
  refine ⟨fun x ⟨e, he, hx⟩ => ?_, fun s hs => ?_⟩
  · subst hx
    have hext := (hpl.externs_ok e he).2
    simp only [beq_false_of_ne (by omega : (pl.ρ e - pl.base).toNat ≠ 1),
      Bool.false_eq_true, ↓reduceIte]
  · have hal := (hpl.symbols_ok s hs).1
    simp only [beq_false_of_ne (by omega : s.2 ≠ 1), Bool.false_eq_true, ↓reduceIte]

theorem _root_.Arm64.Obj.MultiPlacedLib.externAt?_base_add_one_noExterns {lib : Obj.MultiPlacedLib}
    {mpl : Obj.MultiPlacement} {i : Nat}
    {overrides : String → Option (State → State)} {svc : State → State}
    (hpl : lib.Placeable mpl) (hi : i < lib.blocks.length) :
    (lib.blockProgram mpl i (fun _ => none) overrides svc).externAt? (mpl.base i + 1#64) = none := by
  apply Obj.PlacedLib.externAt?_base_add_one_noExterns (lib := lib.blockLib i)
    (pl := lib.blockPlacement mpl i)
  rw [lib.blockLib_text_of_lt hi]
  exact hpl.blocks_ok i hi

theorem _root_.Arm64.Obj.MultiPlacedLib.externAt?_base_add_one_of_pos {lib : Obj.MultiPlacedLib}
    {mpl : Obj.MultiPlacement} {i : Nat}
    {externs overrides : String → Option (State → State)} {svc : State → State}
    (hpl : lib.Placeable mpl) (hi : i < lib.blocks.length) (hpos : 0 < lib.blocks[i].code.length) :
    (lib.blockProgram mpl i externs overrides svc).externAt? (mpl.base i + 1#64) = none := by
  apply Obj.PlacedLib.externAt?_base_add_one_of_pos (lib := lib.blockLib i)
    (pl := lib.blockPlacement mpl i)
  · rw [lib.blockLib_text_of_lt hi]; exact hpl.blocks_ok i hi
  · rw [lib.blockLib_text_of_lt hi]; exact hpos

theorem _root_.Arm64.Obj.MultiPlacedLib.CodeLoaded.blockProgram {lib : Obj.MultiPlacedLib}
    {mpl : Obj.MultiPlacement} {m : Memory} (hL : lib.CodeLoaded mpl m)
    {i : Nat} (hi : i < lib.blocks.length)
    {externs overrides : String → Option (State → State)} {svc : State → State} :
    (lib.blockProgram mpl i externs overrides svc).CodeLoaded m :=
  (hL i hi).of_base_code rfl rfl

theorem _root_.Arm64.Obj.MultiPlacedLib.CodeLoaded.of_keepsFrozen {lib : Obj.MultiPlacedLib}
    {mpl : Obj.MultiPlacement} {m m' : Memory}
    (hL : lib.CodeLoaded mpl m) (hkf : m.KeepsFrozen m') :
    lib.CodeLoaded mpl m' :=
  fun i hi => (hL i hi).of_keepsFrozen hkf

theorem _root_.Arm64.Obj.MultiPlacedLib.loadCodeMem_eq_of_codeLoaded {lib : Obj.MultiPlacedLib}
    {mpl : Obj.MultiPlacement} {m : Memory} {i : Nat}
    {externs overrides : String → Option (State → State)} {svc : State → State}
    (hL : lib.CodeLoaded mpl m) (hi : i < lib.blocks.length) :
    loadCodeMem (lib.blockProgram mpl i externs overrides svc) m = m :=
  ProofLib.loadCodeMem_eq_of_codeLoaded (hL.blockProgram hi)

theorem _root_.Arm64.Obj.MultiPlacedLib.restoreCodeMem_eq_of_codeLoaded {lib : Obj.MultiPlacedLib}
    {mpl : Obj.MultiPlacement} {m0 mf : Memory} {i : Nat}
    {externs overrides : String → Option (State → State)} {svc : State → State}
    (hL0 : lib.CodeLoaded mpl m0) (hLf : lib.CodeLoaded mpl mf) (hi : i < lib.blocks.length) :
    restoreCodeMem (lib.blockProgram mpl i externs overrides svc) m0 mf = mf :=
  ProofLib.restoreCodeMem_eq_of_codeLoaded (hL0.blockProgram hi) (hLf.blockProgram hi)

theorem _root_.Arm64.Obj.MultiPlacedLib.subroutineHookEntry_mem_of_codeLoaded
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {i : Nat}
    {entry_pc : BitVec 64} {s0 : State}
    {externs overrides : String → Option (State → State)} {svc : State → State}
    (hL : lib.CodeLoaded mpl s0.mem) (hi : i < lib.blocks.length) :
    (subroutineHookEntry (lib.blockProgram mpl i externs overrides svc) entry_pc s0).mem = s0.mem :=
  ProofLib.subroutineHookEntry_mem_of_codeLoaded (hL.blockProgram hi)

theorem _root_.Arm64.Obj.MultiPlacedLib.subroutineHookExit_mem_of_codeLoaded
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {i : Nat} {s0 sf' : State}
    {externs overrides : String → Option (State → State)} {svc : State → State}
    (hL0 : lib.CodeLoaded mpl s0.mem) (hLf : lib.CodeLoaded mpl sf'.mem)
    (hi : i < lib.blocks.length) :
    (subroutineHookExit (lib.blockProgram mpl i externs overrides svc) s0 sf').mem = sf'.mem :=
  ProofLib.subroutineHookExit_mem_of_codeLoaded (hL0.blockProgram hi) (hLf.blockProgram hi)

theorem _root_.Arm64.Obj.sepAll_nil : Obj.sepAll [] = emp := rfl

theorem _root_.Arm64.Obj.sepAll_cons (p : SepProp) (ps : List SepProp) :
    Obj.sepAll (p :: ps) = p ∗ Obj.sepAll ps := by
  cases ps with
  | nil => exact (sepConj_emp p).symm
  | cons _ _ => rfl

theorem _root_.Arm64.Obj.sepAll_dup {ps : List SepProp} (hdup : ∀ p ∈ ps, (p ∗ p) = p) :
    (Obj.sepAll ps ∗ Obj.sepAll ps) = Obj.sepAll ps := by
  induction ps with
  | nil => exact emp_sepConj emp
  | cons p rest ih =>
    rw [Obj.sepAll_cons]
    exact sepConj_dup (hdup p (by simp)) (ih fun q hq => hdup q (by simp [hq]))

theorem _root_.Arm64.Obj.satisfies_sepAll_intro {m : Memory} {ps : List SepProp} {P : SepProp}
    (hall : ∀ p ∈ ps, ∀ Q, (m ⊨ Q) → (m ⊨ p ∗ Q)) (hP : m ⊨ P) :
    m ⊨ Obj.sepAll ps ∗ P := by
  induction ps generalizing P with
  | nil => rw [Obj.sepAll_nil, emp_sepConj]; exact hP
  | cons p rest ih =>
    rw [Obj.sepAll_cons, sepConj_assoc]
    exact hall p (by simp) _ (ih (fun q hq => hall q (by simp [hq])) hP)

theorem _root_.Arm64.Obj.sepAll_focus {ps : List SepProp} {p : SepProp} (hp : p ∈ ps) :
    ∃ Q, Obj.sepAll ps = p ∗ Q := by
  induction ps with
  | nil => cases hp
  | cons q rest ih =>
    rw [Obj.sepAll_cons]
    rcases List.mem_cons.mp hp with rfl | hmem
    · exact ⟨Obj.sepAll rest, rfl⟩
    · obtain ⟨Q, hQ⟩ := ih hmem
      exact ⟨q ∗ Q, by rw [hQ, sepConj_left_comm]⟩

theorem _root_.Arm64.Program.CodeLoaded.rx {prog : Program} {m : Memory}
    (hL : prog.CodeLoaded m) : m.RX prog.base prog.code.length := by
  intro a ha
  have hk : (a - prog.base).toNat < prog.code.length := ha
  have heq : prog.base + BitVec.ofNat 64 (a - prog.base).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  rw [← heq]
  exact ⟨hL.perm_eq _ hk, hL.isLazyFree_eq _ hk⟩

theorem _root_.Arm64.Program.CodeLoaded.readBytes_eq {prog : Program} {m : Memory}
    (hL : prog.CodeLoaded m) : m.readBytes prog.base prog.code.length = prog.code :=
  Memory.readBytes_of_read8 fun i hi => hL.byte_eq i hi

/-- Introduce read-only code ownership `(prog.base ↦ᵣ prog.code)` onto any assertion `P` satisfied
    by `m` whenever `prog.CodeLoaded m` holds (with no `DisjointRegions` or `SepProp.NoRO` side
    condition). -/
theorem Satisfies.codeRO_intro {prog : Program} {m : Memory} {P : SepProp}
    (hL : prog.CodeLoaded m) (hP : m ⊨ P) :
    m ⊨ (prog.base ↦ᵣ prog.code) ∗ P :=
  (IsBlockRO.pointsToBytesRO prog.base prog.code (by have := hL.no_wrap; omega)).intro_of_rx
    hL.rx hL.readBytes_eq hP

@[simp]
theorem _root_.Arm64.Obj.MultiPlacedLib.codeRO_dup (lib : Obj.MultiPlacedLib)
    (mpl : Obj.MultiPlacement) :
    (lib.codeRO mpl ∗ lib.codeRO mpl) = lib.codeRO mpl := by
  apply Obj.sepAll_dup
  intro p hp
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  exact pointsToBytesRO_dup _ _

theorem _root_.Arm64.Obj.MultiPlacedLib.blockCodeRO_eq_of_lt {lib : Obj.MultiPlacedLib}
    {mpl : Obj.MultiPlacement} {i : Nat} (hi : i < lib.blocks.length) :
    lib.blockCodeRO mpl i =
      ((mpl.base i) ↦ᵣ (lib.blocks[i].patched (lib.blockPlacement mpl i))) := by
  simp [Obj.MultiPlacedLib.blockCodeRO, lib.blockLib_text_of_lt hi]

/-- Introduce read-only code ownership `lib.blockCodeRO mpl i` for block `i < lib.blocks.length`
    onto any `m ⊨ P` whenever `lib.CodeLoaded mpl m` holds. -/
theorem _root_.Arm64.Obj.MultiPlacedLib.satisfies_blockCodeRO_of_codeLoaded
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {m : Memory} {P : SepProp} {i : Nat}
    (hL : lib.CodeLoaded mpl m) (hi : i < lib.blocks.length) (hP : m ⊨ P) :
    m ⊨ lib.blockCodeRO mpl i ∗ P := by
  simpa [Obj.MultiPlacedLib.blockCodeRO, Obj.MultiPlacedLib.blockProgram,
    Obj.MultiPlacedLib.blockPlacement, Obj.PlacedLib.program_base, Obj.PlacedLib.program_code] using
    Satisfies.codeRO_intro (hL i hi) hP

/-- Introduce read-only code ownership `lib.codeRO mpl` across all blocks of `lib` onto any
    `m ⊨ P` whenever `lib.CodeLoaded mpl m` holds. -/
theorem _root_.Arm64.Obj.MultiPlacedLib.satisfies_codeRO_of_codeLoaded
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {m : Memory} {P : SepProp}
    (hL : lib.CodeLoaded mpl m) (hP : m ⊨ P) :
    m ⊨ lib.codeRO mpl ∗ P := by
  apply Obj.satisfies_sepAll_intro _ hP
  intro p hp Q hQ
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  exact lib.satisfies_blockCodeRO_of_codeLoaded hL (List.mem_range.mp hi) hQ

theorem _root_.Arm64.Obj.MultiPlacedLib.satisfies_codeRO_of_codeLoaded'
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {m : Memory}
    (hL : lib.CodeLoaded mpl m) : m ⊨ lib.codeRO mpl := by
  simpa [sepConj_emp] using lib.satisfies_codeRO_of_codeLoaded hL (satisfies_emp m)

private theorem read8_of_readBytes_eq {m : Memory} {base : BitVec 64} {bs : List (BitVec 8)}
    (h : m.readBytes base bs.length = bs) (k : Nat) (hk : k < bs.length) :
    m.read8 (base + BitVec.ofNat 64 k) = bs[k] := by
  induction bs generalizing base k with
  | nil => cases hk
  | cons b rest ih =>
    simp only [List.length_cons, Memory.readBytes_succ, List.cons.injEq] at h
    cases k with
    | zero => simpa using h.1
    | succ k' =>
      have hk' : k' < rest.length := by simp at hk; omega
      have hadd : base + BitVec.ofNat 64 (k' + 1) = (base + 1#64) + BitVec.ofNat 64 k' := by
        bv_arith
      rw [hadd, ih h.2 k' hk']
      rfl

theorem _root_.Arm64.Obj.MultiPlacedLib.CodeLoaded.permsRX {lib : Obj.MultiPlacedLib}
    {mpl : Obj.MultiPlacement} {m : Memory}
    (hpl : lib.Placeable mpl) (hL : lib.CodeLoaded mpl m) : lib.PermsRX mpl m := by
  intro i hi
  have hrx : m.RX (mpl.base i)
      ((lib.blockLib i).text.patched (lib.blockPlacement mpl i)).length := (hL i hi).rx
  have hlen : ((lib.blockLib i).text.patched (lib.blockPlacement mpl i)).length =
      lib.blocks[i].code.length := by
    rw [lib.blockLib_text_of_lt hi]
    exact Obj.CodeBlock.length_patched_of_aligned _ (hpl.blocks_ok i hi).len_aligned
  rwa [hlen] at hrx

/-- Converse per-block bridge: read-only byte ownership `lib.blockCodeRO mpl i` (`↦ᵣ`) together
    with `m.RX` and `lib.Placeable mpl` recovers `(lib.blockProgram mpl i ...).CodeLoaded m`. -/
theorem _root_.Arm64.Obj.MultiPlacedLib.blockCodeLoaded_of_pointsToBytesRO
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {m : Memory} {R : SepProp} {i : Nat}
    {externs overrides : String → Option (State → State)} {svc : State → State}
    (hpl : lib.Placeable mpl) (hi : i < lib.blocks.length)
    (hrx : m.RX (mpl.base i) lib.blocks[i].code.length)
    (hsat : m ⊨ lib.blockCodeRO mpl i ∗ R) :
    (lib.blockProgram mpl i externs overrides svc).CodeLoaded m := by
  have hbi := hpl.blocks_ok i hi
  have hbase_al : (mpl.base i).toNat % 4 = 0 := by
    have ⟨_, ha4⟩ := hbi.align_pos
    have hba : (mpl.base i).toNat % lib.blocks[i].align = 0 := hbi.base_aligned
    exact Nat.dvd_trans (Nat.dvd_of_mod_eq_zero ha4) (Nat.dvd_of_mod_eq_zero hba)
      |> Nat.mod_eq_zero_of_dvd
  have hlen_eq : ((lib.blockLib i).text.patched (lib.blockPlacement mpl i)).length =
      lib.blocks[i].code.length := by
    rw [lib.blockLib_text_of_lt hi]
    exact Obj.CodeBlock.length_patched_of_aligned _ hbi.len_aligned
  have hnw : (mpl.base i).toNat + lib.blocks[i].code.length ≤ 2 ^ 64 := hbi.no_wrap
  have hread : m.readBytes (mpl.base i)
      ((lib.blockLib i).text.patched (lib.blockPlacement mpl i)).length =
      (lib.blockLib i).text.patched (lib.blockPlacement mpl i) :=
    (IsBlockRO.pointsToBytesRO (mpl.base i) _ (by omega)).read hsat
  refine Program.CodeLoaded.intro hbase_al
    (show (mpl.base i).toNat + ((lib.blockLib i).text.patched (lib.blockPlacement mpl i)).length ≤
        2 ^ 64 by omega)
    fun k hk => ?_
  have hk_pat : k < ((lib.blockLib i).text.patched (lib.blockPlacement mpl i)).length := hk
  have hk_code : k < lib.blocks[i].code.length := by omega
  have hin : InRegion (mpl.base i) lib.blocks[i].code.length (mpl.base i + BitVec.ofNat 64 k) := by
    simp only [InRegion]
    have hsub : mpl.base i + BitVec.ofNat 64 k - mpl.base i = BitVec.ofNat 64 k := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel]
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hk_code
  refine ⟨?_, ?_⟩
  · simpa [Obj.MultiPlacedLib.blockProgram, Obj.MultiPlacedLib.blockPlacement,
      Obj.PlacedLib.program] using read8_of_readBytes_eq hread k hk_pat
  · simpa [Obj.MultiPlacedLib.blockProgram, Obj.MultiPlacedLib.blockPlacement,
      Obj.PlacedLib.program] using hrx _ hin

/-- Converse multi-block bridge: `lib.codeRO mpl` (`↦ᵣ` across all blocks) together with
    `lib.PermsRX mpl m` and `lib.Placeable mpl` recovers `lib.CodeLoaded mpl m`. -/
theorem _root_.Arm64.Obj.MultiPlacedLib.codeLoaded_of_codeRO {lib : Obj.MultiPlacedLib}
    {mpl : Obj.MultiPlacement} {m : Memory} {R : SepProp}
    (hpl : lib.Placeable mpl) (hrx : lib.PermsRX mpl m)
    (hsat : m ⊨ lib.codeRO mpl ∗ R) :
    lib.CodeLoaded mpl m := by
  intro i hi
  have hmem : lib.blockCodeRO mpl i ∈ (List.range lib.blocks.length).map (lib.blockCodeRO mpl) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  obtain ⟨Q, hQ⟩ := Obj.sepAll_focus hmem
  have hsat_i : m ⊨ lib.blockCodeRO mpl i ∗ (Q ∗ R) := by
    simpa only [Obj.MultiPlacedLib.codeRO, hQ, sepConj_assoc] using hsat
  exact lib.blockCodeLoaded_of_pointsToBytesRO hpl hi (hrx i hi) hsat_i

/-- Exact characterization of `lib.CodeLoaded mpl m` in terms of read-only byte ownership
    `lib.codeRO mpl` (`↦ᵣ`) and `lib.PermsRX mpl m` under `lib.Placeable mpl`. -/
theorem _root_.Arm64.Obj.MultiPlacedLib.codeLoaded_iff_codeRO {lib : Obj.MultiPlacedLib}
    {mpl : Obj.MultiPlacement} {m : Memory} (hpl : lib.Placeable mpl) :
    lib.CodeLoaded mpl m ↔ lib.PermsRX mpl m ∧ (m ⊨ lib.codeRO mpl) :=
  ⟨fun hL => ⟨hL.permsRX hpl, lib.satisfies_codeRO_of_codeLoaded' hL⟩,
   fun ⟨hrx, hsat⟩ => lib.codeLoaded_of_codeRO hpl hrx (by rwa [sepConj_emp])⟩

/-- Lift a multi-block placed library contract `lib.subroutineOk fnName innerSpec externs overrides`
    at a `Placeable` placement `mpl` to `HookOk (lib.subroutineHook mpl fnName externs overrides) spec`
    when `lib.CodeLoaded mpl s0.mem` holds at hook entry, with no `memRegion` or `SepProp.NoRO`
    requirement (fully compatible with caller `↦ᵣ` / `lib.codeRO mpl` ownership). -/
theorem subroutineHook_ok_of_multiCodeLoaded {S β : Type} [ToBaseSpec S β]
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {fnName : String}
    {innerSpec : Obj.MultiPlacement → S} {spec : Spec β}
    {externs overrides : String → Option (State → State)}
    (h_pl : lib.Placeable mpl)
    (h_sub : lib.subroutineOk fnName innerSpec externs overrides)
    (h_pre : ∀ x s0,
      spec.pre x s0 ⊢
        ⌜lib.CodeLoaded mpl s0.mem⌝ ∗
        (ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).pre x
          (subroutineHookEntry
            (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides)
            (lib.fnAddr mpl fnName) s0))
    (h_post : ∀ x s0 sf',
      lib.CodeLoaded mpl s0.mem →
      (⌜lib.CodeLoaded mpl sf'.mem⌝ ∗
        (ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).post x
          (subroutineHookEntry
            (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides)
            (lib.fnAddr mpl fnName) s0) sf') ⊢
        spec.post x s0
          (subroutineHookExit
            (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides) s0 sf'))
    (h_ext1 :
        externs = (fun _ => none) ∨
        0 < (lib.blockLib (lib.fnBlockIdx fnName)).text.code.length ∨
        (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides).externAt?
          (mpl.base (lib.fnBlockIdx fnName) + 1#64) = none := by
      first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl (by decide)))
    (h_no_panic : ∀ x R' s0 sf', sf'.status = .Panicked →
      ¬(sf'.mem ⊨
        (ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).onPanic x
          (subroutineHookEntry
            (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides)
            (lib.fnAddr mpl fnName) s0) sf' ∗ R') := by
      intro _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ x code R' s0 sf', sf'.status = .Exited code →
      ¬(sf'.mem ⊨
        (ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).onExit x code
          (subroutineHookEntry
            (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides)
            (lib.fnAddr mpl fnName) s0) sf' ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ x s0 sf',
      lib.CodeLoaded mpl s0.mem →
      lib.CodeLoaded mpl sf'.mem →
      sf'.status = .OutOfMemory →
      (ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))).onOom x
        (subroutineHookEntry
          (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides)
          (lib.fnAddr mpl fnName) s0) sf' ⊢
        spec.onOom x s0
          (subroutineHookExit
            (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides) s0 sf') := by
      intro _ _ _ _ _ _
      try simp only [Spec.codeLoadedMultiSubroutineHook,
        Obj.MultiPlacedLib.codeLoadedSubroutineHook, Spec.allowOom]
      exact Entails.refl _) :
    HookOk (lib.subroutineHook mpl fnName externs overrides) spec := by
  obtain ⟨_, idx, off, hlook, hall⟩ := h_sub
  have hidx : lib.fnBlockIdx fnName = idx := lib.fnBlockIdx_eq_of_lookup hlook
  have hi : idx < lib.blocks.length := lookupBlockSym_lt hlook
  rw [lib.subroutineHook_eq_of_lookup hlook]
  cases hidx
  let prog := lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides
  let inner := ToBaseSpec.toSpec (innerSpec mpl) (mpl.base (lib.fnBlockIdx fnName))
  intro x R s0 hrun hpre_sat hsp
  have hpre_framed : s0.mem ⊨
      (⌜lib.CodeLoaded mpl s0.mem⌝ ∗
        inner.pre x (subroutineHookEntry prog (lib.fnAddr mpl fnName) s0)) ∗ R :=
    Satisfies.mono (sepConj_mono_left (h_pre x s0)) hpre_sat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_framed
  rcases hpre_framed with ⟨hL0, hin_pre⟩
  let s0' := subroutineHookEntry prog (lib.fnAddr mpl fnName) s0
  have hp0 : prog.CodeLoaded s0.mem := hL0.blockProgram hi
  have hs0'_mem : s0'.mem = s0.mem := subroutineHookEntry_mem_of_codeLoaded hp0
  have hL0' : lib.CodeLoaded mpl s0'.mem := hs0'_mem ▸ hL0
  have hp0' : prog.CodeLoaded s0'.mem := hs0'_mem ▸ hp0
  have hs0'_pre : s0'.mem ⊨ (lib.withCodeLoaded mpl inner).pre x s0' ∗ R := by
    dsimp only [Obj.MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm (inner.pre x s0'), sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hL0', hs0'_mem ▸ hin_pre⟩
  have hs0'_sp : s0'.spAligned = true := by
    simpa [s0', subroutineHookEntry, State.spAligned, State.setMem, State.setPC,
      State.writeReg64] using hsp
  obtain ⟨sf', h_steps, hout⟩ := reaches_outcome_iff.1 (subroutine_ok_iff.1 (hall mpl h_pl) x R s0' rfl hrun hs0'_pre hs0'_sp) hp0'
  have hLf : lib.CodeLoaded mpl sf'.mem := hL0'.of_keepsFrozen h_steps.keepsFrozen
  have hpf : prog.CodeLoaded sf'.mem := hLf.blockProgram hi
  have hsf_mem : (subroutineHookExit prog s0 sf').mem = sf'.mem :=
    subroutineHookExit_mem_of_codeLoaded hp0 hpf
  have hext1 : prog.externAt? (mpl.base (lib.fnBlockIdx fnName) + 1#64) = none := by
    rcases h_ext1 with rfl | hpos | hext
    · exact lib.externAt?_base_add_one_noExterns h_pl hi
    · rw [lib.blockLib_text_of_lt hi] at hpos
      exact lib.externAt?_base_add_one_of_pos h_pl hi hpos
    · exact hext
  have hhook_eq : subroutineHook prog (lib.fnAddr mpl fnName) s0 = subroutineHookExit prog s0 sf' :=
    subroutineHook_eq_of_steps_outcome hp0.aligned hext1 h_steps hout
  rw [hhook_eq]
  have hkf : s0.mem.KeepsFrozen (subroutineHookExit prog s0 sf').mem := by
    rw [← hs0'_mem, hsf_mem]
    exact h_steps.keepsFrozen
  have hsym : (subroutineHookExit prog s0 sf').symtab = s0.symtab := by
    rw [subroutineHookExit_symtab, h_steps.symtab_eq, subroutineHookEntry_symtab]
  rcases hout with ⟨hret, hcc, hpost_sat⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine ⟨hkf, hsym, Or.inl ⟨subroutineHookExit_returned hret, subroutineHookExit_cc hcc, ?_⟩⟩
    rw [hsf_mem]
    have h_comb : sf'.mem ⊨ (⌜lib.CodeLoaded mpl sf'.mem⌝ ∗ inner.post x s0' sf') ∗ R := by
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hLf, hpost_sat⟩
    exact Satisfies.mono (sepConj_mono_left (h_post x s0 sf' hL0)) h_comb
  · exact False.elim (h_no_panic x R s0 sf' hpan hq)
  · exact False.elim (h_no_exit x code R s0 sf' hex hq)
  · refine ⟨hkf, hsym, Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))⟩
    · simp [subroutineHookExit, hoom, State.setMem, State.writeReg64]
    · rw [hsf_mem]
      exact Satisfies.mono (sepConj_mono_left (h_oom x s0 sf' hL0 hLf hoom)) hq

theorem subroutineHook_ok_codeLoadedMultiSubroutineHook {S β : Type} [ToBaseSpec S β]
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
    (h_no_panic : ∀ x R' s0 sf', sf'.status = .Panicked →
      ¬(sf'.mem ⊨
        (ToBaseSpec.toSpec (spec mpl) (mpl.base (lib.fnBlockIdx fnName))).onPanic x
          (subroutineHookEntry
            (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides)
            (lib.fnAddr mpl fnName) s0) sf' ∗ R') := by
      intro _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ x code R' s0 sf', sf'.status = .Exited code →
      ¬(sf'.mem ⊨
        (ToBaseSpec.toSpec (spec mpl) (mpl.base (lib.fnBlockIdx fnName))).onExit x code
          (subroutineHookEntry
            (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides)
            (lib.fnAddr mpl fnName) s0) sf' ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ x s0 sf',
      lib.CodeLoaded mpl s0.mem →
      lib.CodeLoaded mpl sf'.mem →
      sf'.status = .OutOfMemory →
      (ToBaseSpec.toSpec (spec mpl) (mpl.base (lib.fnBlockIdx fnName))).onOom x
        (subroutineHookEntry
          (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides)
          (lib.fnAddr mpl fnName) s0) sf' ⊢
        (Spec.codeLoadedMultiSubroutineHook lib mpl fnName spec externs overrides).onOom x s0
          (subroutineHookExit
            (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides) s0 sf') := by
      intro _ _ _ _ _ _
      try simp only [Spec.codeLoadedMultiSubroutineHook,
        Obj.MultiPlacedLib.codeLoadedSubroutineHook, Spec.allowOom]
      exact Entails.refl _) :
    HookOk (lib.subroutineHook mpl fnName externs overrides)
      (Spec.codeLoadedMultiSubroutineHook lib mpl fnName spec externs overrides) := by
  have hi : lib.fnBlockIdx fnName < lib.blocks.length := lib.fnBlockIdx_lt_of_subroutineOk h_sub
  refine subroutineHook_ok_of_multiCodeLoaded h_pl h_sub
    (fun _ _ => Entails.refl _)
    (fun _ s0 sf' hL0 => ?_)
    h_ext1 h_no_panic h_no_exit h_oom
  refine Entails.pure_left fun hLf => ?_
  have hLf_exit : lib.CodeLoaded mpl
      (subroutineHookExit
        (lib.blockProgram mpl (lib.fnBlockIdx fnName) externs overrides) s0 sf').mem := by
    rwa [lib.subroutineHookExit_mem_of_codeLoaded hL0 hLf hi]
  exact Entails.sepExists_right sf' (Entails.pure_right ⟨rfl, hLf_exit⟩ (Entails.refl _))

/-- Split a `SepWP` proof at `mid`, re-establishing `lib.CodeLoaded mpl sm.mem` across any
    preceding instructions (including memory stores and `KeepsFrozen` hooks). -/
theorem SepWP.seq_multiCodeLoaded {prog : Program} {lib : Obj.MultiPlacedLib}
    {mpl : Obj.MultiPlacement} {mid target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hL : lib.CodeLoaded mpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      lib.CodeLoaded mpl sm.mem →
      SepWP prog target_pc sm Pm post oom) oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm hLp
  rcases h R hm hLp with ⟨sm, hst1, ⟨_, _, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hst2, hout⟩ :=
      hcont (hL.of_keepsFrozen hst1.keepsFrozen) R hmm (hst1.codeLoaded hLp)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact ⟨sm, hst1, Or.inr hoom⟩

/-- Postcondition weakening for `SepWP` supplying `lib.CodeLoaded mpl sf.mem` at `target_pc`
    from `lib.CodeLoaded mpl s.mem` at start state `s`. -/
theorem SepWP.mono_multiCodeLoaded {prog : Program} {lib : Obj.MultiPlacedLib}
    {mpl : Obj.MultiPlacement} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {post post' : State → SepProp → Prop} {oom : State → SepProp}
    (hL : lib.CodeLoaded mpl s.mem)
    (h : SepWP prog target_pc s P post oom)
    (himp : ∀ sf Pf, sf.pc = target_pc → sf.status = .Running →
      lib.CodeLoaded mpl sf.mem → post sf Pf → post' sf Pf) :
    SepWP prog target_pc s P post' oom := by
  intro R hm hLp
  rcases h R hm hLp with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hp⟩ | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf,
      himp sf Pf hpc hrun (hL.of_keepsFrozen hsteps.keepsFrozen) hp⟩⟩
  · exact ⟨sf, hsteps, Or.inr hoom⟩

end ProofLib
