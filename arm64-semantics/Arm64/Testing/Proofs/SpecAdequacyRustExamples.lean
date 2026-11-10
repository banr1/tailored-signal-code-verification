/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import Arm64.Testing.Generators.CompiledBinaryFixture
public import Arm64.Testing.Generators.AdequacyTourFixture
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.Check

/-!
# Operational Hoare-Triple Proofs for the Spec Adequacy Tour

Proves the operational Hoare triples and precondition-satisfiability witnesses for the Rust
programs in [`Arm64/Testing/Tours/SpecAdequacyTour.lean`](../Tours/SpecAdequacyTour.lean).
-/

@[expose] public section

namespace Arm64.Testing.SpecAdequacyTour

open Arm64
open ProofLib
open ProofLib.Disproof
open ProofLib.ProgramReflection
open ProofLib.GenPlacedFetches
open Testing.Generators

abbrev examplesLib : Obj.PlacedLib := fixturePlacedLib

set_option maxRecDepth 200000

def adeqTextProg : Program :=
  { code := adequacy_tourLib.text.code, symbols := adequacy_tourLib.text.symbols }

def adeqText_tree : WordTree := word_tree_of% adeqTextProg

theorem adeqText_code_eq : adequacy_tourLib.text.code = adeqText_tree.toBytes := by rfl_kernel

theorem adeqText_tree_size : adeqText_tree.checkSize? = some 99 := by rfl_kernel

def adeqText_symChars : List (List Char × Nat) := sym_chars_of% adeqTextProg

theorem adeqText_symbols_eq :
    adequacy_tourLib.text.symbols = toStringSymbols adeqText_symChars := by rfl_kernel

theorem adeqText_symbols_fresh : allFreshCharSymbols adeqText_symChars = true := by rfl_kernel

class AdeqPlacement where
  pl : Obj.Placement
  placeable : adequacy_tourLib.Placeable pl

def adeqCC [AdeqPlacement] : Program := adequacy_tourLib.program AdeqPlacement.pl

gen_placed_fetches adeqCC adequacy_tourLib adeqText_tree adeqText_code_eq
  adeqText_tree_size via_placement AdeqPlacement.pl AdeqPlacement.placeable
  [0x0 → 0x188]
gen_placed_fnOffs adeqCC adequacy_tourLib adeqText_symChars adeqText_symbols_eq
  adeqText_symbols_fresh

def exTextProg : Program :=
  { code := examplesLib.text.code, symbols := examplesLib.text.symbols }

def exText_tree : WordTree := word_tree_of% exTextProg

theorem exText_code_eq : examplesLib.text.code = exText_tree.toBytes := by rfl_kernel

theorem exText_tree_size : exText_tree.checkSize? = some 568 := by rfl_kernel

def exText_symChars : List (List Char × Nat) := sym_chars_of% exTextProg

theorem exText_symbols_eq :
    examplesLib.text.symbols = toStringSymbols exText_symChars := by rfl_kernel

theorem exText_symbols_fresh : allFreshCharSymbols exText_symChars = true := by rfl_kernel

class ExPlacement where
  pl : Obj.Placement
  placeable : examplesLib.Placeable pl

def exCC [ExPlacement] : Program := examplesLib.program ExPlacement.pl

gen_placed_fetches exCC examplesLib exText_tree exText_code_eq
  exText_tree_size via_placement ExPlacement.pl ExPlacement.placeable
  [0x6b8 → 0x6e0]
gen_placed_fnOffs exCC examplesLib exText_symChars exText_symbols_eq
  exText_symbols_fresh

theorem safe_until_of_steps {prog : Program} {s₀ s' : State}
    (hsteps : Steps prog s₀ s') :
    ∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t :=
  fun _ ht => Steps.running_or_steps_of hsteps ht

theorem not_running_after_nonrunning {prog : Program} {s' t : State}
    (hnonrun : s'.status ≠ .Running) (hsteps : Steps prog s' t) :
    t.status ≠ .Running := by
  cases hsteps with
  | refl => exact hnonrun
  | step hstep _ => exact absurd hstep.status_running hnonrun

/-- Panic hook table mapping both demangled Rust panic symbols (`Rust.isPanicSymbol`) and their
    mangled v0 `.symtab` extern names in `PlacedLib` to `Rust.panicked`. -/
def tourWithPanics (hooks : String → Option (State → State) := fun _ => none) :
    String → Option (State → State) :=
  Rust.withPanics fun name =>
    if name = "_RNvNtCskxtBwYRO61I_4core9panicking5panic" ||
       name = "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" then
      some Rust.panicked
    else
      hooks name

theorem findSome?_externs_const {X : String → Option (State → State)} {f : State → State}
    {g : String → Nat} {k : Nat} :
    ∀ {L : List String} {e : String},
      e ∈ L → g e = k → (∀ e' ∈ L, X e' = some f) →
      (L.map fun e' => (e', g e')).findSome?
        (fun (p : String × Nat) => if p.2 == k then X p.1 else none) = some f
  | [], _, he, _, _ => nomatch he
  | a :: L, e, he, hge, hX => by
    simp only [List.map_cons, List.findSome?_cons, hX a (List.mem_cons_self ..)]
    cases h : (g a == k)
    · rcases List.mem_cons.1 he with rfl | heL
      · simp [hge] at h
      · exact findSome?_externs_const heL hge fun e' he' => hX e' (List.mem_cons_of_mem _ he')
    · rfl

theorem externAt?_rebase_const {lib : Obj.PlacedLib} {pl : Obj.Placement}
    {X : String → Option (State → State)} {f : State → State} {e : String}
    (he : e ∈ lib.text.externs)
    (hX : ∀ e' ∈ lib.text.externs, X e' = some f) :
    ((lib.program pl).rebase pl.base X).externAt?
      (pl.base + (pl.ρ e - pl.base)) = some f := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase Obj.PlacedLib.program
  dsimp only
  have hsub : pl.base + (pl.ρ e - pl.base) - pl.base = pl.ρ e - pl.base := by bv_omega
  rw [hsub, findSome?_externs_const (g := fun e' => (pl.ρ e' - pl.base).toNat) he rfl hX]
  rfl

theorem tourWithPanics_examples_all (e : String) (he : e ∈ examplesLib.text.externs) :
    tourWithPanics (fun _ => none) e = some Rust.panicked := by
  change e ∈ ["_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check",
    "_RNvNtCskxtBwYRO61I_4core9panicking5panic"] at he
  rcases List.mem_cons.1 he with rfl | he
  · simp [tourWithPanics, Rust.withPanics, Rust.isPanicSymbol]
  · rcases List.mem_cons.1 he with rfl | he
    · simp [tourWithPanics, Rust.withPanics, Rust.isPanicSymbol]
    · nomatch he

theorem tourWithPanics_adequacy_all (e : String) (he : e ∈ adequacy_tourLib.text.externs) :
    tourWithPanics (fun _ => none) e = some Rust.panicked := by
  change e ∈ ["_RNvNtCskxtBwYRO61I_4core9panicking5panic"] at he
  rcases List.mem_cons.1 he with rfl | he
  · simp [tourWithPanics, Rust.withPanics, Rust.isPanicSymbol]
  · nomatch he

theorem exCC_externAt?_panic [ExPlacement] :
    (exCC.rebase ExPlacement.pl.base tourWithPanics).externAt?
      (ExPlacement.pl.base +
        (ExPlacement.pl.ρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic" - ExPlacement.pl.base)) =
      some Rust.panicked :=
  externAt?_rebase_const (by decide) tourWithPanics_examples_all

theorem adeqCC_externAt?_panic [AdeqPlacement] :
    (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).externAt?
      (AdeqPlacement.pl.base +
        (AdeqPlacement.pl.ρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic" - AdeqPlacement.pl.base)) =
      some Rust.panicked :=
  externAt?_rebase_const (by decide) tourWithPanics_adequacy_all

@[local simp, local arm64_norm]
theorem exCC_svc [ExPlacement] : exCC.svc = Syscall.standard := by
  funext s; cases s; rfl

@[local simp, local arm64_norm]
theorem adeqCC_svc [AdeqPlacement] : adeqCC.svc = Syscall.standard := by
  funext s; cases s; rfl

theorem reaches_pc_of_pairStep {prog : Program} {tgt pc1 pc2 : BitVec 64} {s : State}
    {rd : BitVec 5} {v : BitVec 64} {Q : State → Prop}
    (hstep : ∀ {t : BitVec 64} {s0 : State} {P : SepProp} {post : State → SepProp → Prop}
      {oom : State → SepProp},
      s0.pc = pc1 → s0.status = .Running →
      SepWP prog t ((s0.writeReg64 (.gpr rd) v).setPC pc2) P post oom →
      SepWP prog t s0 P post oom)
    (hpc : s.pc = pc1) (hrun : s.status = .Running)
    (hnext : reaches_pc prog tgt ((s.writeReg64 (.gpr rd) v).setPC pc2) Q) :
    reaches_pc prog tgt s Q := by
  have hwp : SepWP prog pc2 s emp
      (fun sf _ => sf = (s.writeReg64 (.gpr rd) v).setPC pc2) :=
    hstep hpc hrun (SepWP.done (State.pc_setPC _ _)
      (by simpa [State.writeReg64, State.setPC] using hrun) rfl)
  have h1 := SepWP.to_reaches_pc (R := emp) hwp (by simp)
  intro hcode
  rcases h1 hcode with ⟨sm, hsteps1, ⟨_, _, _, _, rfl⟩ | ⟨_, hoom⟩⟩
  · rcases hnext (hsteps1.codeLoaded hcode) with ⟨sf, hsteps2, hout⟩
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · simp at hoom

theorem steps_to_panicked_of_reaches_stub {prog : Program} {stub_pc : BitVec 64} {s₀ : State}
    (hcode : prog.CodeLoaded s₀.mem)
    (hext : prog.externAt? stub_pc = some Rust.panicked)
    (hreach : reaches_pc prog stub_pc s₀ (fun _ => True)) :
    ∃ s' : State, Steps prog s₀ s' ∧ s'.status = .Panicked := by
  rcases hreach hcode with ⟨s₁, hsteps₁, ⟨hpc₁, hrun₁, _⟩ | ⟨_, hoom⟩⟩
  · have hstep_pan : Step prog s₁ (Rust.panicked s₁) :=
      Step.extern hrun₁ (hpc₁ ▸ hext) (Memory.KeepsFrozen.refl _) rfl
    exact ⟨Rust.panicked s₁, hsteps₁.trans (.step hstep_pan (.refl _)), rfl⟩
  · exact False.elim hoom

theorem steps_exec_of_reaches_pc {prog : Program} {pc₁ : BitVec 64} {inst : Instr}
    {s₀ : State} {P Q : State → Prop}
    (hcode : prog.CodeLoaded s₀.mem)
    (hfetch : prog.fetch pc₁ = some inst)
    (hreach : reaches_pc prog pc₁ s₀ P)
    (hq : ∀ s₁, s₁.pc = pc₁ → s₁.status = .Running → prog.CodeLoaded s₁.mem → P s₁ →
      Q (prog.evalInst inst s₁)) :
    ∃ s' : State, Steps prog s₀ s' ∧ Q s' := by
  rcases hreach hcode with ⟨s₁, hsteps₁, ⟨hpc₁, hrun₁, hP⟩ | ⟨_, hoom⟩⟩
  · have hcode₁ : prog.CodeLoaded s₁.mem := hsteps₁.codeLoaded hcode
    have hstep : Step prog s₁ (prog.evalInst inst s₁) :=
      Step.exec hrun₁ (Program.fetchMem_of_fetch hcode₁ (hpc₁ ▸ hfetch))
    exact ⟨prog.evalInst inst s₁, hsteps₁.trans (.step hstep (.refl _)),
      hq s₁ hpc₁ hrun₁ hcode₁ hP⟩
  · exact False.elim hoom

theorem canWrite16_split {m : Memory} {a : BitVec 64} (h : m.canWrite a 16 = true) :
    m.canWrite a 8 = true ∧ m.canWrite (a + 8#64) 8 = true := by
  have hsplit := Memory.allPerm_add m (fun p => p.w && !p.x) a 8 8
  change m.canWrite a 16 = (m.canWrite a 8 && m.canWrite (a + 8#64) 8) at hsplit
  rw [h] at hsplit
  simpa using hsplit.symm

/-! ## Example 1: `examples::functions::bad` (`assert!(x == 0)`) panics when `x ≠ 0` -/

theorem bad_panics_proof (pl : Obj.Placement) (h : examplesLib.Placeable pl)
    (s₀ : State)
    (hstatus : s₀.status = .Running)
    (hpc : s₀.pc = (examplesLib.program pl tourWithPanics).fnAddr "examples::functions::bad")
    (hsp : s₀.readReg64 .sp &&& 0xF#64 = 0#64)
    (hcode : (examplesLib.program pl tourWithPanics).CodeLoaded s₀.mem)
    (hmem : s₀.mem.canWrite (s₀.sp - 16#64) 16 = true)
    (hx : s₀.readReg64 .x0 ≠ 0#64) :
    let prog := examplesLib.program pl tourWithPanics
    ∃ s' : State, Steps prog s₀ s' ∧ s'.status = .Panicked := by
  letI : ExPlacement := ⟨pl, h⟩
  dsimp only
  change s₀.pc = (exCC.rebase ExPlacement.pl.base tourWithPanics).fnAddr "examples::functions::bad" at hpc
  change (exCC.rebase ExPlacement.pl.base tourWithPanics).CodeLoaded s₀.mem at hcode
  change ∃ s' : State, Steps (exCC.rebase ExPlacement.pl.base tourWithPanics) s₀ s' ∧ s'.status = .Panicked
  have hx0 : (s₀.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx
  have hsp' : (s₀.sp &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp
  obtain ⟨hcw1, hcw2⟩ := canWrite16_split hmem
  refine steps_to_panicked_of_reaches_stub hcode exCC_externAt?_panic ?_
  iterate 3 arm64_step
  refine reaches_pc_of_pairStep (exCC_pairStep_0x6c8 ExPlacement.pl.base tourWithPanics rfl)
    (by simp [arm64_norm]) (by simp [arm64_norm, hstatus]) ?_
  refine reaches_pc_of_pairStep (exCC_pairStep_0x6d0 ExPlacement.pl.base tourWithPanics rfl)
    (by simp [arm64_norm]) (by simp [arm64_norm, hstatus]) ?_
  iterate 2 arm64_step
  have hpc_eq : ExPlacement.pl.base + 1756#64 +
      (ExPlacement.pl.ρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic" -
        ExPlacement.pl.base - 1756#64) =
      ExPlacement.pl.base +
        (ExPlacement.pl.ρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic" -
          ExPlacement.pl.base) := by bv_omega
  exact reaches_pc_refl (by simp [arm64_norm, hpc_eq]) (by simp [arm64_norm, hstatus]) trivial

/-! ## Example 2: `assert_getrandom_gt_5()` panics when the `getrandom` byte is `≤ 5` -/

theorem canWrite20_split {m : Memory} {sp : BitVec 64} (h : m.canWrite (sp - 20#64) 20 = true) :
    m.canWrite (sp - 32#64 + 12#64) 1 = true ∧
    m.canWrite (sp - 32#64 + 16#64) 8 = true ∧
    m.canWrite (sp - 32#64 + 24#64) 8 = true := by
  have h1 := Memory.allPerm_add m (fun p => p.w && !p.x) (sp - 20#64) 4 16
  change m.canWrite (sp - 20#64) 20 =
    (m.canWrite (sp - 20#64) 4 && m.canWrite (sp - 20#64 + 4#64) 16) at h1
  rw [h, show sp - 20#64 + 4#64 = sp - 16#64 by bv_lin] at h1
  have ⟨hw4, hw16⟩ : m.canWrite (sp - 20#64) 4 = true ∧ m.canWrite (sp - 16#64) 16 = true := by
    simpa using h1.symm
  have hw1 : m.canWrite (sp - 20#64) 1 = true := Memory.canWrite_take_of_le hw4 (by decide)
  obtain ⟨hw2, hw3⟩ := canWrite16_split hw16
  rw [show sp - 20#64 = sp - 32#64 + 12#64 by bv_lin] at hw1
  rw [show sp - 16#64 + 8#64 = sp - 32#64 + 24#64 by bv_lin] at hw3
  rw [show sp - 16#64 = sp - 32#64 + 16#64 by bv_lin] at hw2
  exact ⟨hw1, hw2, hw3⟩

@[local simp, local arm64_norm]
theorem list_range_one : List.range 1 = [0] := rfl

@[local simp, local arm64_norm]
theorem writeBytes_singleton (m : Memory) (a : BitVec 64) (b : BitVec 8) :
    m.writeBytes a [b] = m.write8 a b := rfl

theorem zeroExtend64_ule_5 {b : BitVec 8} (h : b.ule 5#8 = true) :
    (BitVec.zeroExtend 64 b).ule 5#64 = true := by
  revert b h; decide

theorem assert_getrandom_gt_5_panics_proof (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State)
    (hstatus : s₀.status = .Running)
    (hpc : s₀.pc = (adequacy_tourLib.program pl tourWithPanics).fnAddr "adequacy_tour::assert_getrandom_gt_5")
    (hsp : s₀.readReg64 .sp &&& 0xF#64 = 0#64)
    (hcode : (adequacy_tourLib.program pl tourWithPanics).CodeLoaded s₀.mem)
    (hread : s₀.mem.canRead (s₀.sp - 20#64) 1 = true)
    (hwrite : s₀.mem.canWrite (s₀.sp - 20#64) 20 = true)
    (hrng : (s₀.oracle.getrandom s₀.oracleIdx 0).ule 5#8 = true) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    ∃ s' : State, Steps prog s₀ s' ∧ s'.status = .Panicked := by
  letI : AdeqPlacement := ⟨pl, h⟩
  dsimp only
  change s₀.pc = (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).fnAddr "adequacy_tour::assert_getrandom_gt_5" at hpc
  change (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).CodeLoaded s₀.mem at hcode
  change ∃ s' : State, Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ s' ∧ s'.status = .Panicked
  have hsp' : (s₀.sp &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp
  obtain ⟨hw1, hw2, hw3⟩ := canWrite20_split hwrite
  have hr1 : s₀.mem.canRead (s₀.sp - 32#64 + 12#64) 1 = true := by
    rw [show s₀.sp - 32#64 + 12#64 = s₀.sp - 20#64 by bv_lin]; exact hread
  have hrng64 := zeroExtend64_ule_5 hrng
  refine steps_to_panicked_of_reaches_stub hcode adeqCC_externAt?_panic ?_
  iterate 12 arm64_step
  refine reaches_pc_of_pairStep (adeqCC_pairStep_0xcc AdeqPlacement.pl.base tourWithPanics rfl)
    (by simp [arm64_norm]) (by simp [arm64_norm, hstatus]) ?_
  refine reaches_pc_of_pairStep (adeqCC_pairStep_0xd4 AdeqPlacement.pl.base tourWithPanics rfl)
    (by simp [arm64_norm]) (by simp [arm64_norm, hstatus]) ?_
  iterate 2 arm64_step
  have hpc_eq : AdeqPlacement.pl.base + 224#64 +
      (AdeqPlacement.pl.ρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic" -
        AdeqPlacement.pl.base - 224#64) =
      AdeqPlacement.pl.base +
        (AdeqPlacement.pl.ρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic" -
          AdeqPlacement.pl.base) := by bv_omega
  exact reaches_pc_refl (by simp [arm64_norm, hpc_eq]) (by simp [arm64_norm, hstatus]) trivial

/-! ## Example 3: `mmap_write_and_verify(x: u64)` - safe until return vs. `OutOfMemory` -/

theorem mapZero_page_props {m : Memory} {page : BitVec 64}
    (hmap : m.canMap page 4096 = true) :
    (m.mapZero page 4096).canRead page 8 = true ∧
    (m.mapZero page 4096).canWrite page 8 = true ∧
    (m.mapZero page 4096).read64 page = 0#64 := by
  have hcr : (m.mapZero page 4096).canRead page 8 = true :=
    Memory.canRead_mapZero_sub hmap (by simp) (by decide)
  have hcw : (m.mapZero page 4096).canWrite page 8 = true :=
    Memory.canWrite_mapZero_sub hmap (by simp) (by decide)
  have hb (k : BitVec 64) (hk : (page + k - page).toNat < 4096) :
      (m.mapZero page 4096).read8 (page + k) = 0#8 :=
    Memory.read8_mapZero_of_canMap hmap hk
  have h0 : (m.mapZero page 4096).read8 page = 0#8 := by
    simpa using hb 0#64 (by bv_omega)
  have h1 : (m.mapZero page 4096).read8 (page + 1#64) = 0#8 := hb 1#64 (by bv_omega)
  have h2 : (m.mapZero page 4096).read8 (page + 2#64) = 0#8 := hb 2#64 (by bv_omega)
  have h3 : (m.mapZero page 4096).read8 (page + 3#64) = 0#8 := hb 3#64 (by bv_omega)
  have h4 : (m.mapZero page 4096).read8 (page + 4#64) = 0#8 := hb 4#64 (by bv_omega)
  have h5 : (m.mapZero page 4096).read8 (page + 5#64) = 0#8 := hb 5#64 (by bv_omega)
  have h6 : (m.mapZero page 4096).read8 (page + 6#64) = 0#8 := hb 6#64 (by bv_omega)
  have h7 : (m.mapZero page 4096).read8 (page + 7#64) = 0#8 := hb 7#64 (by bv_omega)
  refine ⟨hcr, hcw, ?_⟩
  simp [Memory.read64, h0, h1, h2, h3, h4, h5, h6, h7]

theorem mmap_write_and_verify_safe_proof (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State)
    (hstatus : s₀.status = .Running)
    (hpc : s₀.pc = (adequacy_tourLib.program pl tourWithPanics).fnAddr "adequacy_tour::mmap_write_and_verify")
    (_hsp : s₀.readReg64 .sp &&& 0xF#64 = 0#64)
    (hcode : (adequacy_tourLib.program pl tourWithPanics).CodeLoaded s₀.mem)
    (hmin : MMAP_MIN_ADDR ≤ (s₀.oracle.mmap s₀.oracleIdx).toNat)
    (halign : (s₀.oracle.mmap s₀.oracleIdx).toNat % 4096 = 0)
    (hva : (s₀.oracle.mmap s₀.oracleIdx).toNat + 4096 ≤ 2 ^ 48)
    (hmap : s₀.mem.canMap (s₀.oracle.mmap s₀.oracleIdx) 4096 = true)
    (hphys : 4096 ≤ s₀.physMemAvail) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    ∃ s' : State,
      Steps prog s₀ s' ∧
      s'.status = .Running ∧
      s'.pc = s₀.readReg64 .x30 ∧
      (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) := by
  letI : AdeqPlacement := ⟨pl, h⟩
  dsimp only
  change s₀.pc = (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).fnAddr "adequacy_tour::mmap_write_and_verify" at hpc
  change (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).CodeLoaded s₀.mem at hcode
  change ∃ s' : State,
    Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ s' ∧
    s'.status = .Running ∧
    s'.pc = s₀.readReg64 .x30 ∧
    (∀ t : State, Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ t →
      t.status = .Running ∨ Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s' t)
  have hsan : sanitizeMmapAddr s₀.mem (s₀.oracle.mmap s₀.oracleIdx) 4096 =
      some (s₀.oracle.mmap s₀.oracleIdx) := by
    unfold sanitizeMmapAddr
    have hvalid :
        (decide (MMAP_MIN_ADDR ≤ (s₀.oracle.mmap s₀.oracleIdx).toNat) &&
         (s₀.oracle.mmap s₀.oracleIdx).toNat % PAGE_SIZE == 0 &&
         decide ((s₀.oracle.mmap s₀.oracleIdx).toNat + 4096 ≤ USER_VA_LIMIT) &&
         s₀.mem.canMap (s₀.oracle.mmap s₀.oracleIdx) 4096) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq, PAGE_SIZE, USER_VA_LIMIT]
      exact ⟨⟨⟨decide_eq_true hmin, halign⟩, decide_eq_true hva⟩, hmap⟩
    rw [hvalid]
    rfl
  have hphys_not_lt : decide (s₀.physMemAvail < 4096) = false :=
    decide_eq_false (by omega)
  obtain ⟨hcr, hcw, hrd0⟩ := mapZero_page_props hmap
  have hreach : reaches_pc (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics)
      (s₀.readReg64 .x30) s₀ (fun _ => True) := by
    iterate 18 arm64_step
    exact reaches_pc_refl (by simp [arm64_norm]) (by simp [arm64_norm, hstatus]) trivial
  rcases hreach hcode with ⟨s', hsteps, ⟨hpc', hrun', _⟩ | ⟨_, hoom⟩⟩
  · exact ⟨s', hsteps, hrun', hpc', safe_until_of_steps hsteps⟩
  · exact False.elim hoom

theorem mmap_write_and_verify_oom_proof (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State)
    (hstatus : s₀.status = .Running)
    (hpc : s₀.pc = (adequacy_tourLib.program pl tourWithPanics).fnAddr "adequacy_tour::mmap_write_and_verify")
    (_hsp : s₀.readReg64 .sp &&& 0xF#64 = 0#64)
    (hcode : (adequacy_tourLib.program pl tourWithPanics).CodeLoaded s₀.mem)
    (hoom : sanitizeMmapAddr s₀.mem (s₀.oracle.mmap s₀.oracleIdx) 4096 = none) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    ∃ s' : State,
      Steps prog s₀ s' ∧
      s'.status = .OutOfMemory ∧
      (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) := by
  letI : AdeqPlacement := ⟨pl, h⟩
  dsimp only
  change s₀.pc = (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).fnAddr "adequacy_tour::mmap_write_and_verify" at hpc
  change (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).CodeLoaded s₀.mem at hcode
  change ∃ s' : State,
    Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ s' ∧
    s'.status = .OutOfMemory ∧
    (∀ t : State, Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ t →
      t.status = .Running ∨ Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s' t)
  obtain ⟨s', hsteps, hst⟩ :
      ∃ s' : State, Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ s' ∧
        s'.status = .OutOfMemory := by
    refine steps_exec_of_reaches_pc hcode (adeqCC_rebase_fetch_0x104 AdeqPlacement.pl.base tourWithPanics)
      (P := fun s₁ =>
        s₁.readReg64 (Reg.gpr 8#5) = 222#64 ∧
        s₁.readReg64 (Reg.gpr 1#5) = 4096#64 ∧
        s₁.readReg64 (Reg.gpr 2#5) = 3#64 ∧
        s₁.readReg64 (Reg.gpr 3#5) = 34#64 ∧
        s₁.readReg64 (Reg.gpr 5#5) = 0#64 ∧
        s₁.mem = s₀.mem ∧
        s₁.oracle = s₀.oracle ∧
        s₁.oracleIdx = s₀.oracleIdx) ?_ ?_
    · iterate 8 arm64_step
      exact reaches_pc_refl (by simp [arm64_norm, hpc]) (by simp [arm64_norm, hstatus])
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], rfl, rfl, rfl⟩
    · rintro s₁ _ _ _ ⟨hx8, hx1, hx2, hx3, hx5, hmem₁, hor, hidx⟩
      simp [execMmap, MMAP_PROT_RW, MMAP_FLAGS_PRIVATE_ANON,
        arm64_norm, hx8, hx1, hx2, hx3, hx5, hmem₁, hor, hidx, hoom]
  exact ⟨s', hsteps, hst, safe_until_of_steps hsteps⟩

/-! ## Example 4: `nonzero_exit_one(x: u64) -> !` exits the process with status `1` -/

theorem nonzero_exit_one_proof (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State)
    (hstatus : s₀.status = .Running)
    (hpc : s₀.pc = (adequacy_tourLib.program pl tourWithPanics).fnAddr "adequacy_tour::nonzero_exit_one")
    (_hsp : s₀.readReg64 .sp &&& 0xF#64 = 0#64)
    (hcode : (adequacy_tourLib.program pl tourWithPanics).CodeLoaded s₀.mem)
    (hx : s₀.readReg64 .x0 ≠ 0#64) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    ∃ s' : State,
      Steps prog s₀ s' ∧
      s'.status = .Exited 1#64 ∧
      (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) := by
  letI : AdeqPlacement := ⟨pl, h⟩
  dsimp only
  change s₀.pc = (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).fnAddr "adequacy_tour::nonzero_exit_one" at hpc
  change (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).CodeLoaded s₀.mem at hcode
  change ∃ s' : State,
    Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ s' ∧
    s'.status = .Exited 1#64 ∧
    (∀ t : State, Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ t →
      t.status = .Running ∨ Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s' t)
  have hexit : exits_with (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) 1#64 s₀
      (fun _ => True) := by
    iterate 4 arm64_step
    exact exits_with_refl (by simp [arm64_norm, hx]) trivial
  rcases hexit hcode with ⟨s', hsteps, ⟨hst, _⟩ | ⟨_, hoom⟩⟩
  · exact ⟨s', hsteps, hst, safe_until_of_steps hsteps⟩
  · exact False.elim hoom

/-! ## Example 5: `read_fixed_addr()` faults when `0xdeadbeef0000` is unmapped -/

theorem read_fixed_addr_faults_proof (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State)
    (hstatus : s₀.status = .Running)
    (hpc : s₀.pc = (adequacy_tourLib.program pl tourWithPanics).fnAddr "adequacy_tour::read_fixed_addr")
    (_hsp : s₀.readReg64 .sp &&& 0xF#64 = 0#64)
    (hcode : (adequacy_tourLib.program pl tourWithPanics).CodeLoaded s₀.mem)
    (hunmapped : s₀.mem.canRead 0xdeadbeef0000#64 8 = false) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    ∃ s' : State, ∃ msg : String, Steps prog s₀ s' ∧ s'.status = .Exception msg := by
  letI : AdeqPlacement := ⟨pl, h⟩
  dsimp only
  change s₀.pc = (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).fnAddr "adequacy_tour::read_fixed_addr" at hpc
  change (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).CodeLoaded s₀.mem at hcode
  change ∃ s' : State, ∃ msg : String, Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ s' ∧ s'.status = .Exception msg
  obtain ⟨s', hsteps, msg, hst⟩ :
      ∃ s' : State, Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ s' ∧
        ∃ msg : String, s'.status = .Exception msg := by
    refine steps_exec_of_reaches_pc hcode (adeqCC_rebase_fetch_0x18 AdeqPlacement.pl.base tourWithPanics)
      (P := fun s₁ => s₁.mem = s₀.mem ∧ s₁.readReg64 .x8 = 0xdeadbeef0000#64) ?_ ?_
    · iterate 2 arm64_step
      exact reaches_pc_refl (by simp [arm64_norm, hpc]) (by simp [arm64_norm, hstatus])
        ⟨rfl, by simp [arm64_norm]⟩
    · rintro s₁ _ _ _ ⟨hmem₁, hx8⟩
      have hx8' : s₁.readReg64 (Reg.gpr 8#5) = 0xdeadbeef0000#64 := hx8
      refine ⟨"permission fault", ?_⟩
      simp [execInst, execInstWithSvc, arm64_norm, hx8', hmem₁, hunmapped]
  exact ⟨s', msg, hsteps, hst⟩

/-! ## Example 6: `verify_own_code_bytes()` reads its own `nop` instruction and returns safely -/

theorem adequacy_tour_nop_canRead_and_read32 [AdeqPlacement] {m : Memory}
    (hcode : (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).CodeLoaded m) :
    m.canRead (AdeqPlacement.pl.base + 336#64) 4 = true ∧
    m.read32 (AdeqPlacement.pl.base + 336#64) = 0xd503201f#32 := by
  let prog := adeqCC.rebase AdeqPlacement.pl.base tourWithPanics
  have hread : prog.readWordOff 336 = some 0xd503201f#32 :=
    Obj.CodeBlock.readWordOff_patched (blk := adequacy_tourLib.text) (pl := AdeqPlacement.pl)
      rfl (by decide) (by decide)
  obtain ⟨h0, h1, h2, h3⟩ :=
    (Program.readWordOff_eq_some_iff prog 336 0xd503201f#32 (by decide)).mp hread
  obtain ⟨hi0, hb0'⟩ := List.getElem?_eq_some_iff.mp h0
  obtain ⟨hi1, hb1'⟩ := List.getElem?_eq_some_iff.mp h1
  obtain ⟨hi2, hb2'⟩ := List.getElem?_eq_some_iff.mp h2
  obtain ⟨hi3, hb3'⟩ := List.getElem?_eq_some_iff.mp h3
  have hp0 : m.perm (AdeqPlacement.pl.base + 336#64) = some Perm.rx := hcode.perm_eq 336 hi0
  have hp1 : m.perm (AdeqPlacement.pl.base + 337#64) = some Perm.rx := hcode.perm_eq 337 hi1
  have hp2 : m.perm (AdeqPlacement.pl.base + 338#64) = some Perm.rx := hcode.perm_eq 338 hi2
  have hp3 : m.perm (AdeqPlacement.pl.base + 339#64) = some Perm.rx := hcode.perm_eq 339 hi3
  have hlf0 : m.isLazyFree (AdeqPlacement.pl.base + 336#64) = false := hcode.isLazyFree_eq 336 hi0
  have hlf1 : m.isLazyFree (AdeqPlacement.pl.base + 337#64) = false := hcode.isLazyFree_eq 337 hi1
  have hlf2 : m.isLazyFree (AdeqPlacement.pl.base + 338#64) = false := hcode.isLazyFree_eq 338 hi2
  have hlf3 : m.isLazyFree (AdeqPlacement.pl.base + 339#64) = false := hcode.isLazyFree_eq 339 hi3
  have hb0 : m.read8 (AdeqPlacement.pl.base + 336#64) = 0x1f#8 := (hcode.byte_eq 336 hi0).trans hb0'
  have hb1 : m.read8 (AdeqPlacement.pl.base + 337#64) = 0x20#8 := (hcode.byte_eq 337 hi1).trans hb1'
  have hb2 : m.read8 (AdeqPlacement.pl.base + 338#64) = 0x03#8 := (hcode.byte_eq 338 hi2).trans hb2'
  have hb3 : m.read8 (AdeqPlacement.pl.base + 339#64) = 0xd5#8 := (hcode.byte_eq 339 hi3).trans hb3'
  refine ⟨?_, ?_⟩
  · simp [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree, hp0, hp1, hp2, hp3,
      hlf0, hlf1, hlf2, hlf3, Perm.rx]
  · simp [Memory.read32, hb0, hb1, hb2, hb3]

theorem verify_own_code_bytes_safe_proof (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State)
    (hstatus : s₀.status = .Running)
    (hpc : s₀.pc = (adequacy_tourLib.program pl tourWithPanics).fnAddr "adequacy_tour::verify_own_code_bytes")
    (_hsp : s₀.readReg64 .sp &&& 0xF#64 = 0#64)
    (hcode : (adequacy_tourLib.program pl tourWithPanics).CodeLoaded s₀.mem) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    ∃ s' : State,
      Steps prog s₀ s' ∧
      s'.status = .Running ∧
      s'.pc = s₀.readReg64 .x30 ∧
      (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) := by
  letI : AdeqPlacement := ⟨pl, h⟩
  dsimp only
  change s₀.pc = (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).fnAddr "adequacy_tour::verify_own_code_bytes" at hpc
  change (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).CodeLoaded s₀.mem at hcode
  change ∃ s' : State,
    Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ s' ∧
    s'.status = .Running ∧
    s'.pc = s₀.readReg64 .x30 ∧
    (∀ t : State, Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ t →
      t.status = .Running ∨ Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s' t)
  obtain ⟨hcr, hrd⟩ := adequacy_tour_nop_canRead_and_read32 hcode
  have hreach : reaches_pc (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics)
      (s₀.readReg64 .x30) s₀ (fun _ => True) := by
    iterate 8 arm64_step
    exact reaches_pc_refl (by simp [arm64_norm]) (by simp [arm64_norm, hstatus]) trivial
  rcases hreach hcode with ⟨s', hsteps, ⟨hpc', hrun', _⟩ | ⟨_, hoom⟩⟩
  · exact ⟨s', hsteps, hrun', hpc', safe_until_of_steps hsteps⟩
  · exact False.elim hoom

/-! ## Example 7: `write_own_code_bytes()` faults when attempting to overwrite `.rx` code -/

theorem write_own_code_bytes_faults_proof (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State)
    (hstatus : s₀.status = .Running)
    (hpc : s₀.pc = (adequacy_tourLib.program pl tourWithPanics).fnAddr "adequacy_tour::write_own_code_bytes")
    (_hsp : s₀.readReg64 .sp &&& 0xF#64 = 0#64)
    (hcode : (adequacy_tourLib.program pl tourWithPanics).CodeLoaded s₀.mem) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    ∃ s' : State, ∃ msg : String, Steps prog s₀ s' ∧ s'.status = .Exception msg := by
  letI : AdeqPlacement := ⟨pl, h⟩
  dsimp only
  change s₀.pc = (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).fnAddr "adequacy_tour::write_own_code_bytes" at hpc
  change (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).CodeLoaded s₀.mem at hcode
  change ∃ s' : State, ∃ msg : String, Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ s' ∧ s'.status = .Exception msg
  have hlen : (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).code.length = 396 := by
    change (adequacy_tourLib.text.patched AdeqPlacement.pl).length = 396
    exact Obj.CodeBlock.length_patched_of_aligned AdeqPlacement.pl (by decide)
  have hperm : s₀.mem.perm (AdeqPlacement.pl.base + 136#64) = some Perm.rx :=
    hcode.perm_eq 136 (by rw [hlen]; decide)
  have hnowrite : s₀.mem.canWrite (AdeqPlacement.pl.base + 136#64) 4 = false := by
    simp [Memory.canWrite, Memory.allPerm, hperm, Perm.rx]
  obtain ⟨s', hsteps, msg, hst⟩ :
      ∃ s' : State, Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ s' ∧
        ∃ msg : String, s'.status = .Exception msg := by
    refine steps_exec_of_reaches_pc hcode (adeqCC_rebase_fetch_0x84 AdeqPlacement.pl.base tourWithPanics)
      (P := fun s₁ => s₁.mem = s₀.mem ∧ s₁.readReg64 (Reg.gpr 9#5) = AdeqPlacement.pl.base + 136#64) ?_ ?_
    · iterate 3 arm64_step
      exact reaches_pc_refl (by simp [arm64_norm, hpc]) (by simp [arm64_norm, hstatus])
        ⟨rfl, by simp [arm64_norm]⟩
    · rintro s₁ _ _ _ ⟨hmem₁, hx9⟩
      refine ⟨"permission fault", ?_⟩
      simp [execInst, execInstWithSvc, arm64_norm, hx9, hmem₁, hnowrite]
  exact ⟨s', msg, hsteps, hst⟩

/-! ## Example 8: `stack_spill_verify(x: u64)` - SP alignment fault vs. aligned safety -/

theorem sp_sub32_and15 (sp : BitVec 64) : (sp - 32#64) &&& 15#64 = sp &&& 15#64 := by
  bv_bits

theorem canWrite24_split {m : Memory} {sp : BitVec 64} (h : m.canWrite (sp - 24#64) 24 = true) :
    m.canWrite (sp - 32#64 + 8#64) 8 = true ∧
    m.canWrite (sp - 32#64 + 16#64) 8 = true ∧
    m.canWrite (sp - 32#64 + 24#64) 8 = true := by
  have h1 := Memory.allPerm_add m (fun p => p.w && !p.x) (sp - 24#64) 8 16
  change m.canWrite (sp - 24#64) 24 =
    (m.canWrite (sp - 24#64) 8 && m.canWrite (sp - 24#64 + 8#64) 16) at h1
  rw [h, show sp - 24#64 + 8#64 = sp - 16#64 by bv_lin] at h1
  have ⟨hw1, hw16⟩ : m.canWrite (sp - 24#64) 8 = true ∧ m.canWrite (sp - 16#64) 16 = true := by
    simpa using h1.symm
  obtain ⟨hw2, hw3⟩ := canWrite16_split hw16
  rw [show sp - 24#64 = sp - 32#64 + 8#64 by bv_lin] at hw1
  rw [show sp - 16#64 + 8#64 = sp - 32#64 + 24#64 by bv_lin] at hw3
  rw [show sp - 16#64 = sp - 32#64 + 16#64 by bv_lin] at hw2
  exact ⟨hw1, hw2, hw3⟩

theorem canRead24_split {m : Memory} {sp : BitVec 64} (h : m.canRead (sp - 24#64) 24 = true) :
    m.canRead (sp - 32#64 + 8#64) 8 = true ∧
    m.canRead (sp - 32#64 + 16#64) 8 = true ∧
    m.canRead (sp - 32#64 + 24#64) 8 = true := by
  have h1p := Memory.allPerm_add m (·.r) (sp - 24#64) 8 16
  have h1l := Memory.allNoLazyFree_add m (sp - 24#64) 8 16
  have ⟨hr1, hr16⟩ : m.canRead (sp - 24#64) 8 = true ∧ m.canRead (sp - 16#64) 16 = true := by
    rw [show (24 : Nat) = 8 + 16 from rfl] at h
    unfold Memory.canRead at h ⊢
    rw [h1p, h1l, show sp - 24#64 + BitVec.ofNat 64 8 = sp - 16#64 by bv_lin] at h
    revert h; simp only [Bool.and_eq_true]; rintro ⟨⟨hp8, hp16⟩, ⟨hl8, hl16⟩⟩
    exact ⟨⟨hp8, hl8⟩, ⟨hp16, hl16⟩⟩
  have h2p := Memory.allPerm_add m (·.r) (sp - 16#64) 8 8
  have h2l := Memory.allNoLazyFree_add m (sp - 16#64) 8 8
  have ⟨hr2, hr3⟩ : m.canRead (sp - 16#64) 8 = true ∧ m.canRead (sp - 32#64 + 24#64) 8 = true := by
    rw [show (16 : Nat) = 8 + 8 from rfl] at hr16
    unfold Memory.canRead at hr16 ⊢
    rw [h2p, h2l, show sp - 16#64 + BitVec.ofNat 64 8 = sp - 32#64 + 24#64 by bv_lin] at hr16
    revert hr16; simp only [Bool.and_eq_true]; rintro ⟨⟨hp8, hp8'⟩, ⟨hl8, hl8'⟩⟩
    exact ⟨⟨hp8, hl8⟩, ⟨hp8', hl8'⟩⟩
  rw [show sp - 24#64 = sp - 32#64 + 8#64 by bv_lin] at hr1
  rw [show sp - 16#64 = sp - 32#64 + 16#64 by bv_lin] at hr2
  exact ⟨hr1, hr2, hr3⟩

theorem stack_spill_verify_unaligned_faults_proof (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State)
    (hstatus : s₀.status = .Running)
    (hpc : s₀.pc = (adequacy_tourLib.program pl tourWithPanics).fnAddr "adequacy_tour::stack_spill_verify")
    (hcode : (adequacy_tourLib.program pl tourWithPanics).CodeLoaded s₀.mem)
    (hunaligned : s₀.readReg64 .sp &&& 0xF#64 ≠ 0#64) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    ∃ s' : State, ∃ msg : String, Steps prog s₀ s' ∧ s'.status = .Exception msg := by
  letI : AdeqPlacement := ⟨pl, h⟩
  dsimp only
  change s₀.pc = (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).fnAddr "adequacy_tour::stack_spill_verify" at hpc
  change (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).CodeLoaded s₀.mem at hcode
  change ∃ s' : State, ∃ msg : String, Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ s' ∧ s'.status = .Exception msg
  have hunaligned' : s₀.sp &&& 15#64 ≠ 0#64 := hunaligned
  obtain ⟨s', hsteps, msg, hst⟩ :
      ∃ s' : State, Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ s' ∧
        ∃ msg : String, s'.status = .Exception msg := by
    refine steps_exec_of_reaches_pc hcode (adeqCC_rebase_fetch_0x38 AdeqPlacement.pl.base tourWithPanics)
      (P := fun s₁ => s₁.sp = s₀.sp - 32#64) ?_ ?_
    · arm64_step
      exact reaches_pc_refl (by simp [arm64_norm, hpc]) (by simp [arm64_norm, hstatus])
        (by simp [arm64_norm])
    · rintro s₁ _ _ _ hsp₁
      refine ⟨"SP alignment fault", ?_⟩
      simp [execInst, execInstWithSvc, arm64_norm, hsp₁, hunaligned']
  exact ⟨s', msg, hsteps, hst⟩

theorem stack_spill_verify_safe_proof (pl : Obj.Placement) (h : adequacy_tourLib.Placeable pl)
    (s₀ : State)
    (hstatus : s₀.status = .Running)
    (hpc : s₀.pc = (adequacy_tourLib.program pl tourWithPanics).fnAddr "adequacy_tour::stack_spill_verify")
    (hsp : s₀.readReg64 .sp &&& 0xF#64 = 0#64)
    (hcode : (adequacy_tourLib.program pl tourWithPanics).CodeLoaded s₀.mem)
    (hread : s₀.mem.canRead (s₀.sp - 24#64) 24 = true)
    (hwrite : s₀.mem.canWrite (s₀.sp - 24#64) 24 = true) :
    let prog := adequacy_tourLib.program pl tourWithPanics
    ∃ s' : State,
      Steps prog s₀ s' ∧
      s'.status = .Running ∧
      s'.pc = s₀.readReg64 .x30 ∧
      (∀ t : State, Steps prog s₀ t → t.status = .Running ∨ Steps prog s' t) := by
  letI : AdeqPlacement := ⟨pl, h⟩
  dsimp only
  change s₀.pc = (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).fnAddr "adequacy_tour::stack_spill_verify" at hpc
  change (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics).CodeLoaded s₀.mem at hcode
  change ∃ s' : State,
    Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ s' ∧
    s'.status = .Running ∧
    s'.pc = s₀.readReg64 .x30 ∧
    (∀ t : State, Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s₀ t →
      t.status = .Running ∨ Steps (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics) s' t)
  have hsp' : (s₀.sp &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp
  have hsp_sub : ((s₀.sp - 32#64) &&& 15#64 == 0#64) = true := by
    rw [sp_sub32_and15]; exact hsp'
  obtain ⟨hw1, hw2, hw3⟩ := canWrite24_split hwrite
  obtain ⟨hr1, hr2, hr3⟩ := canRead24_split hread
  have hreach : reaches_pc (adeqCC.rebase AdeqPlacement.pl.base tourWithPanics)
      (s₀.readReg64 .x30) s₀ (fun _ => True) := by
    iterate 11 arm64_step
    exact reaches_pc_refl (by simp [arm64_norm]) (by simp [arm64_norm, hstatus]) trivial
  rcases hreach hcode with ⟨s', hsteps, ⟨hpc', hrun', _⟩ | ⟨_, hoom⟩⟩
  · exact ⟨s', hsteps, hrun', hpc', safe_until_of_steps hsteps⟩
  · exact False.elim hoom

/-! ## Precondition-Satisfiability Witnesses (Non-Vacuity) -/

def tourPerm (codeLen : Nat) (a : BitVec 64) : Option Perm :=
  if (a - 0x10000#64).toNat < codeLen then some Perm.rx
  else if (a - 0x2ffe0#64).toNat < 32 then some Perm.rw
  else none

def tourDummyMem (codeLen : Nat) : Memory :=
  Memory.ofFn (fun _ => 0#8) (tourPerm codeLen)

def tourStackMem : Memory :=
  Memory.ofFn (fun _ => 0#8)
    (fun a => if (a - 0x2ffe0#64).toNat < 32 then some Perm.rw else none)

theorem perm_loadCode_tourStackMem (prog : Program) {codeLen : Nat}
    (hbase : prog.base = 0x10000#64) (hlen : prog.code.length = codeLen) :
    (prog.loadCode tourStackMem).perm = (tourDummyMem codeLen).perm := by
  funext a
  simp [Program.loadCode, tourStackMem, tourDummyMem, tourPerm, hbase, hlen]

theorem isLazyFree_loadCode_tourStackMem (prog : Program) {codeLen : Nat} :
    (prog.loadCode tourStackMem).isLazyFree = (tourDummyMem codeLen).isLazyFree := by
  funext a
  have h1 : (prog.loadCode tourStackMem).isLazyFree a = false := by
    unfold Program.loadCode
    rw [Memory.isLazyFree_ofFn, tourStackMem, Memory.perm_ofFn]
    by_cases hc : (a - prog.base).toNat < prog.code.toArray.size
    · simp only [hc, ↓reduceIte]; rfl
    · by_cases hs : (a - 0x2ffe0#64).toNat < 32 <;> simp only [hc, hs, ↓reduceIte] <;> rfl
  have h2 : (tourDummyMem codeLen).isLazyFree a = false := by
    unfold tourDummyMem
    rw [Memory.isLazyFree_ofFn]
    unfold tourPerm
    by_cases hc : (a - 0x10000#64).toNat < codeLen
    · simp only [hc, ↓reduceIte]; rfl
    · by_cases hs : (a - 0x2ffe0#64).toNat < 32 <;> simp only [hc, hs, ↓reduceIte] <;> rfl
  exact h1.trans h2.symm

theorem tourDummyMem_canMap_0x50000 :
    (tourDummyMem 396).canMap 0x50000#64 4096 = true := by
  unfold Memory.canMap
  rw [Memory.allPerm_iff]
  intro i hi
  have h1 : ¬ (0x50000#64 + BitVec.ofNat 64 i - 0x10000#64).toNat < 396 := by bv_omega
  have h2 : ¬ (0x50000#64 + BitVec.ofNat 64 i - 0x2ffe0#64).toNat < 32 := by bv_omega
  unfold tourDummyMem
  rw [Memory.perm_ofFn]
  unfold tourPerm
  simp only [h1, h2, ↓reduceIte]
  rfl

def tourPlacement : Obj.Placement where
  base := 0x10000#64
  ρ := fun _ => 0x11000#64

private instance (k : Obj.RelocKind) : Decidable (k = .abs32) :=
  match k with
  | .abs32 => isTrue rfl
  | .call26 | .jump26 | .adrpHi21 | .adrpHi21Nc | .addLo12 | .ldst8Lo12 | .ldst16Lo12
  | .ldst32Lo12 | .ldst64Lo12 | .ldst128Lo12 | .condbr19 | .tstbr14 | .adrPrelLo21
  | .ldPrelLo19 | .adrGotPage | .ld64GotLo12Nc | .tlsieAdrGottprelPage21
  | .tlsieLd64GottprelLo12Nc | .tlsdescAdrPage21 | .tlsdescLd64Lo12 | .tlsdescAddLo12
  | .tlsdescCall | .tlsleAddTprelHi12 | .tlsleAddTprelLo12 | .tlsleAddTprelLo12Nc
  | .tlsleLdst8TprelLo12Nc | .tlsleLdst16TprelLo12Nc | .tlsleLdst32TprelLo12Nc
  | .tlsleLdst64TprelLo12Nc | .tlsleLdst128TprelLo12Nc | .tlsleMovwTprelG1
  | .tlsleMovwTprelG1Nc | .tlsleMovwTprelG0 | .tlsleMovwTprelG0Nc | .abs64
  | .prel32 => isFalse nofun

private instance (k : Obj.RelocKind) : Decidable (k = .prel32) :=
  match k with
  | .prel32 => isTrue rfl
  | .call26 | .jump26 | .adrpHi21 | .adrpHi21Nc | .addLo12 | .ldst8Lo12 | .ldst16Lo12
  | .ldst32Lo12 | .ldst64Lo12 | .ldst128Lo12 | .condbr19 | .tstbr14 | .adrPrelLo21
  | .ldPrelLo19 | .adrGotPage | .ld64GotLo12Nc | .tlsieAdrGottprelPage21
  | .tlsieLd64GottprelLo12Nc | .tlsdescAdrPage21 | .tlsdescLd64Lo12 | .tlsdescAddLo12
  | .tlsdescCall | .tlsleAddTprelHi12 | .tlsleAddTprelLo12 | .tlsleAddTprelLo12Nc
  | .tlsleLdst8TprelLo12Nc | .tlsleLdst16TprelLo12Nc | .tlsleLdst32TprelLo12Nc
  | .tlsleLdst64TprelLo12Nc | .tlsleLdst128TprelLo12Nc | .tlsleMovwTprelG1
  | .tlsleMovwTprelG1Nc | .tlsleMovwTprelG0 | .tlsleMovwTprelG0Nc | .abs64
  | .abs32 => isFalse nofun

private instance (t : BitVec 64) : Decidable (Obj.Abs32InRange t) :=
  inferInstanceAs (Decidable (_ ∧ _))

private instance (p t : BitVec 64) : Decidable (Obj.Prel32InRange p t) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem examples_placeable_tourPlacement :
    examplesLib.Placeable tourPlacement :=
  ⟨Obj.CodeBlock.placeable_of_checkPlaceable (by decide +kernel),
   by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem adequacy_tour_placeable_tourPlacement :
    adequacy_tourLib.Placeable tourPlacement :=
  ⟨Obj.CodeBlock.placeable_of_checkPlaceable (by decide +kernel),
   by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem adequacy_tour_placeable_exists :
    ∃ pl : Obj.Placement, adequacy_tourLib.Placeable pl ∧ pl.base = 0x10000#64 :=
  ⟨tourPlacement, adequacy_tour_placeable_tourPlacement, rfl⟩

theorem examples_placeable_exists :
    ∃ pl : Obj.Placement, examplesLib.Placeable pl ∧ pl.base = 0x10000#64 :=
  ⟨tourPlacement, examples_placeable_tourPlacement, rfl⟩

theorem bad_panics_pre_sat :
    ∃ (pl : Obj.Placement),
      examplesLib.Placeable pl ∧
      ∃ (s₀ : State),
        let prog := examplesLib.program pl tourWithPanics
        s₀.status = .Running ∧
        s₀.pc = prog.fnAddr "examples::functions::bad" ∧
        s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
        prog.CodeLoaded s₀.mem ∧
        s₀.mem.canWrite (s₀.sp - 16#64) 16 = true ∧
        s₀.readReg64 .x0 ≠ 0#64 := by
  let prog := examplesLib.program tourPlacement tourWithPanics
  have hpbase : prog.base = 0x10000#64 := rfl
  have hplen : prog.code.length = 2272 :=
    Obj.CodeBlock.length_patched_of_aligned tourPlacement (by decide)
  let s₀ : State :=
    { regs := RegFile.empty.write 0#5 1#64
      sp := 0x30000#64
      pc := prog.fnAddr "examples::functions::bad"
      mem := prog.loadCode tourStackMem }
  witness pl := tourPlacement, s₀ := s₀, examples_placeable_tourPlacement
  · rfl
  · rfl
  · change (0x30000#64 &&& 0xF#64 : BitVec 64) = 0#64; decide
  · exact prog.codeLoaded_loadCode tourStackMem (by rw [hpbase]; decide) (by rw [hpbase, hplen]; decide)
  · change (prog.loadCode tourStackMem).canWrite (0x30000#64 - 16#64) 16 = true
    rw [Memory.canWrite_congr (perm_loadCode_tourStackMem prog hpbase hplen)]
    decide
  · change ((RegFile.empty.write 0#5 1#64).read 0#5 : BitVec 64) ≠ 0#64; decide

theorem assert_getrandom_gt_5_panics_pre_sat :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::assert_getrandom_gt_5" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem ∧
      s₀.mem.canRead (s₀.sp - 20#64) 1 = true ∧
      s₀.mem.canWrite (s₀.sp - 20#64) 20 = true ∧
      (s₀.oracle.getrandom s₀.oracleIdx 0).ule 5#8 = true := by
  let prog := adequacy_tourLib.program tourPlacement tourWithPanics
  have hpbase : prog.base = 0x10000#64 := rfl
  have hplen : prog.code.length = 396 :=
    Obj.CodeBlock.length_patched_of_aligned tourPlacement (by decide)
  let s₀ : State :=
    { sp := 0x30000#64
      pc := prog.fnAddr "adequacy_tour::assert_getrandom_gt_5"
      mem := prog.loadCode tourStackMem
      oracle := { getrandom := fun _ _ => 3#8 } }
  refine ⟨tourPlacement, s₀, adequacy_tour_placeable_tourPlacement, rfl, rfl,
    by change (0x30000#64 &&& 0xF#64 : BitVec 64) = 0#64; decide, ?_, ?_, ?_, rfl⟩
  · exact prog.codeLoaded_loadCode tourStackMem (by rw [hpbase]; decide) (by rw [hpbase, hplen]; decide)
  · change (prog.loadCode tourStackMem).canRead (0x30000#64 - 20#64) 1 = true
    rw [Memory.canRead_congr (perm_loadCode_tourStackMem prog hpbase hplen)
      (isLazyFree_loadCode_tourStackMem prog)]
    decide
  · change (prog.loadCode tourStackMem).canWrite (0x30000#64 - 20#64) 20 = true
    rw [Memory.canWrite_congr (perm_loadCode_tourStackMem prog hpbase hplen)]
    decide

theorem mmap_write_and_verify_safe_pre_sat :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::mmap_write_and_verify" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem ∧
      MMAP_MIN_ADDR ≤ (s₀.oracle.mmap s₀.oracleIdx).toNat ∧
      (s₀.oracle.mmap s₀.oracleIdx).toNat % 4096 = 0 ∧
      (s₀.oracle.mmap s₀.oracleIdx).toNat + 4096 ≤ 2 ^ 48 ∧
      s₀.mem.canMap (s₀.oracle.mmap s₀.oracleIdx) 4096 = true ∧
      4096 ≤ s₀.physMemAvail := by
  let prog := adequacy_tourLib.program tourPlacement tourWithPanics
  have hpbase : prog.base = 0x10000#64 := rfl
  have hplen : prog.code.length = 396 :=
    Obj.CodeBlock.length_patched_of_aligned tourPlacement (by decide)
  let s₀ : State :=
    { sp := 0x30000#64
      pc := prog.fnAddr "adequacy_tour::mmap_write_and_verify"
      mem := prog.loadCode tourStackMem
      oracle := { mmap := fun _ => 0x50000#64 }
      physMemAvail := 4096 }
  refine ⟨tourPlacement, s₀, adequacy_tour_placeable_tourPlacement, rfl, rfl,
    by change (0x30000#64 &&& 0xF#64 : BitVec 64) = 0#64; decide, ?_,
    by change MMAP_MIN_ADDR ≤ (0x50000#64 : BitVec 64).toNat; decide,
    by change (0x50000#64 : BitVec 64).toNat % 4096 = 0; decide,
    by change (0x50000#64 : BitVec 64).toNat + 4096 ≤ 2 ^ 48; decide, ?_, Nat.le_refl 4096⟩
  · exact prog.codeLoaded_loadCode tourStackMem (by rw [hpbase]; decide) (by rw [hpbase, hplen]; decide)
  · change (prog.loadCode tourStackMem).canMap 0x50000#64 4096 = true
    rw [Memory.canMap_congr (perm_loadCode_tourStackMem prog hpbase hplen)]
    exact tourDummyMem_canMap_0x50000

def tourFullMem : Memory :=
  Memory.ofFn (fun _ => 0#8) (fun _ => some Perm.rw)

private theorem findUnmappedAreaLoop_allMapped {m : Memory}
    (hm : ∀ a, (m.perm a).mapped = true) :
    ∀ fuel addr, findUnmappedAreaLoop m 4096 fuel addr = none
  | 0, _ => rfl
  | fuel + 1, addr => by
    unfold findUnmappedAreaLoop
    split
    · rfl
    · have hfb : findMappedByte m (BitVec.ofNat 64 addr) 0 4096 = some 0 := by
        show (if (m.perm (BitVec.ofNat 64 addr + BitVec.ofNat 64 0)).mapped then some 0
              else findMappedByte m (BitVec.ofNat 64 addr) 1 4095) = some 0
        rw [hm]
        rfl
      simp [hfb, findUnmappedAreaLoop_allMapped hm fuel]

private theorem sanitizeMmapAddr_zero_allMapped {m : Memory}
    (hm : ∀ a, (m.perm a).mapped = true) :
    sanitizeMmapAddr m 0#64 4096 = none := by
  unfold sanitizeMmapAddr findUnmappedArea
  have h1 : (4096 == 0 || 4096 % PAGE_SIZE != 0) = false := by decide
  have h2 : (decide (MMAP_MIN_ADDR ≤ (0#64 : BitVec 64).toNat) &&
      (0#64 : BitVec 64).toNat % PAGE_SIZE == 0 &&
      decide ((0#64 : BitVec 64).toNat + 4096 ≤ USER_VA_LIMIT) && m.canMap 0#64 4096) = false := by
    have hmin : decide (MMAP_MIN_ADDR ≤ (0#64 : BitVec 64).toNat) = false := by decide
    rw [hmin]
    rfl
  rw [h1, h2]
  exact findUnmappedAreaLoop_allMapped hm _ _

theorem mmap_write_and_verify_oom_pre_sat :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::mmap_write_and_verify" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem ∧
      sanitizeMmapAddr s₀.mem (s₀.oracle.mmap s₀.oracleIdx) 4096 = none := by
  obtain ⟨pl, hpl, hbase⟩ := adequacy_tour_placeable_exists
  let prog := adequacy_tourLib.program pl tourWithPanics
  have hpbase : prog.base = 0x10000#64 := hbase
  have hplen : prog.code.length = 396 :=
    Obj.CodeBlock.length_patched_of_aligned pl (by decide)
  let s₀ : State :=
    { sp := 0x30000#64
      pc := prog.fnAddr "adequacy_tour::mmap_write_and_verify"
      mem := prog.loadCode tourFullMem
      oracle := { mmap := fun _ => 0#64 } }
  have hm : ∀ a, ((prog.loadCode tourFullMem).perm a).mapped = true := by
    intro a
    simp only [Program.loadCode, tourFullMem, Memory.perm_ofFn]
    split <;> rfl
  refine ⟨pl, s₀, hpl, rfl, rfl,
    by change (0x30000#64 &&& 0xF#64 : BitVec 64) = 0#64; decide, ?_, ?_⟩
  · exact prog.codeLoaded_loadCode tourFullMem (by rw [hpbase]; decide) (by rw [hpbase, hplen]; decide)
  · exact sanitizeMmapAddr_zero_allMapped hm

theorem nonzero_exit_one_pre_sat :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::nonzero_exit_one" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem ∧
      s₀.readReg64 .x0 ≠ 0#64 := by
  let prog := adequacy_tourLib.program tourPlacement tourWithPanics
  have hpbase : prog.base = 0x10000#64 := rfl
  have hplen : prog.code.length = 396 :=
    Obj.CodeBlock.length_patched_of_aligned tourPlacement (by decide)
  let s₀ : State :=
    { regs := RegFile.empty.write 0#5 42#64
      sp := 0x30000#64
      pc := prog.fnAddr "adequacy_tour::nonzero_exit_one"
      mem := prog.loadCode tourStackMem }
  refine ⟨tourPlacement, s₀, adequacy_tour_placeable_tourPlacement, rfl, rfl,
    by change (0x30000#64 &&& 0xF#64 : BitVec 64) = 0#64; decide, ?_,
    by change ((RegFile.empty.write 0#5 42#64).read 0#5 : BitVec 64) ≠ 0#64; decide⟩
  exact prog.codeLoaded_loadCode tourStackMem (by rw [hpbase]; decide) (by rw [hpbase, hplen]; decide)

theorem read_fixed_addr_faults_pre_sat :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::read_fixed_addr" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem ∧
      s₀.mem.canRead 0xdeadbeef0000#64 8 = false := by
  let prog := adequacy_tourLib.program tourPlacement tourWithPanics
  have hpbase : prog.base = 0x10000#64 := rfl
  have hplen : prog.code.length = 396 :=
    Obj.CodeBlock.length_patched_of_aligned tourPlacement (by decide)
  let s₀ : State :=
    { sp := 0x30000#64
      pc := prog.fnAddr "adequacy_tour::read_fixed_addr"
      mem := prog.loadCode tourStackMem }
  refine ⟨tourPlacement, s₀, adequacy_tour_placeable_tourPlacement, rfl, rfl,
    by change (0x30000#64 &&& 0xF#64 : BitVec 64) = 0#64; decide, ?_, ?_⟩
  · exact prog.codeLoaded_loadCode tourStackMem (by rw [hpbase]; decide) (by rw [hpbase, hplen]; decide)
  · change (prog.loadCode tourStackMem).canRead 0xdeadbeef0000#64 8 = false
    rw [Memory.canRead_congr (perm_loadCode_tourStackMem prog hpbase hplen)
      (isLazyFree_loadCode_tourStackMem prog)]
    decide

theorem verify_own_code_bytes_safe_pre_sat :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::verify_own_code_bytes" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem := by
  let prog := adequacy_tourLib.program tourPlacement tourWithPanics
  have hpbase : prog.base = 0x10000#64 := rfl
  have hplen : prog.code.length = 396 :=
    Obj.CodeBlock.length_patched_of_aligned tourPlacement (by decide)
  let s₀ : State :=
    { sp := 0x30000#64
      pc := prog.fnAddr "adequacy_tour::verify_own_code_bytes"
      mem := prog.loadCode tourStackMem }
  refine ⟨tourPlacement, s₀, adequacy_tour_placeable_tourPlacement, rfl, rfl,
    by change (0x30000#64 &&& 0xF#64 : BitVec 64) = 0#64; decide, ?_⟩
  exact prog.codeLoaded_loadCode tourStackMem (by rw [hpbase]; decide) (by rw [hpbase, hplen]; decide)

theorem write_own_code_bytes_faults_pre_sat :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::write_own_code_bytes" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem := by
  let prog := adequacy_tourLib.program tourPlacement tourWithPanics
  have hpbase : prog.base = 0x10000#64 := rfl
  have hplen : prog.code.length = 396 :=
    Obj.CodeBlock.length_patched_of_aligned tourPlacement (by decide)
  let s₀ : State :=
    { sp := 0x30000#64
      pc := prog.fnAddr "adequacy_tour::write_own_code_bytes"
      mem := prog.loadCode tourStackMem }
  refine ⟨tourPlacement, s₀, adequacy_tour_placeable_tourPlacement, rfl, rfl,
    by change (0x30000#64 &&& 0xF#64 : BitVec 64) = 0#64; decide, ?_⟩
  exact prog.codeLoaded_loadCode tourStackMem (by rw [hpbase]; decide) (by rw [hpbase, hplen]; decide)

theorem stack_spill_verify_unaligned_faults_pre_sat :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::stack_spill_verify" ∧
      prog.CodeLoaded s₀.mem ∧
      s₀.readReg64 .sp &&& 0xF#64 ≠ 0#64 := by
  let prog := adequacy_tourLib.program tourPlacement tourWithPanics
  have hpbase : prog.base = 0x10000#64 := rfl
  have hplen : prog.code.length = 396 :=
    Obj.CodeBlock.length_patched_of_aligned tourPlacement (by decide)
  let s₀ : State :=
    { sp := 0x30008#64
      pc := prog.fnAddr "adequacy_tour::stack_spill_verify"
      mem := prog.loadCode tourStackMem }
  refine ⟨tourPlacement, s₀, adequacy_tour_placeable_tourPlacement, rfl, rfl, ?_,
    by change (0x30008#64 &&& 0xF#64 : BitVec 64) ≠ 0#64; decide⟩
  exact prog.codeLoaded_loadCode tourStackMem (by rw [hpbase]; decide) (by rw [hpbase, hplen]; decide)

theorem stack_spill_verify_safe_pre_sat :
    ∃ (pl : Obj.Placement) (s₀ : State),
      let prog := adequacy_tourLib.program pl tourWithPanics
      adequacy_tourLib.Placeable pl ∧
      s₀.status = .Running ∧
      s₀.pc = prog.fnAddr "adequacy_tour::stack_spill_verify" ∧
      s₀.readReg64 .sp &&& 0xF#64 = 0#64 ∧
      prog.CodeLoaded s₀.mem ∧
      s₀.mem.canRead (s₀.sp - 24#64) 24 = true ∧
      s₀.mem.canWrite (s₀.sp - 24#64) 24 = true := by
  let prog := adequacy_tourLib.program tourPlacement tourWithPanics
  have hpbase : prog.base = 0x10000#64 := rfl
  have hplen : prog.code.length = 396 :=
    Obj.CodeBlock.length_patched_of_aligned tourPlacement (by decide)
  let s₀ : State :=
    { sp := 0x30000#64
      pc := prog.fnAddr "adequacy_tour::stack_spill_verify"
      mem := prog.loadCode tourStackMem }
  refine ⟨tourPlacement, s₀, adequacy_tour_placeable_tourPlacement, rfl, rfl,
    by change (0x30000#64 &&& 0xF#64 : BitVec 64) = 0#64; decide, ?_, ?_, ?_⟩
  · exact prog.codeLoaded_loadCode tourStackMem (by rw [hpbase]; decide) (by rw [hpbase, hplen]; decide)
  · change (prog.loadCode tourStackMem).canRead (0x30000#64 - 24#64) 24 = true
    rw [Memory.canRead_congr (perm_loadCode_tourStackMem prog hpbase hplen)
      (isLazyFree_loadCode_tourStackMem prog)]
    decide
  · change (prog.loadCode tourStackMem).canWrite (0x30000#64 - 24#64) 24 = true
    rw [Memory.canWrite_congr (perm_loadCode_tourStackMem prog hpbase hplen)]
    decide

end Arm64.Testing.SpecAdequacyTour
