/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliSymtabGhost
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# Budget-Threaded CLI `main` Specification and Process Composition

Threads `RustCliAllocBudget M` and `BudgetLimits` through `mainFrame`, `mainEntryPre`, `mainSpec`,
`mainSpecTight`, and the musl process-composition theorems (`outcome_of_main`, `outcome_of_main_or_oom`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.TopBudget

open Arm64 ProofLib
open Arm64.Process
open CryptoVerification.LibsignalTripleRatchet (entryOf)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession (
  CliHooks Inputs cliExterns fsView outcomeOf outcomeOf_eq_aborted outcomeOf_eq_exited
  symtabGhost_ofImage_cliExterns
)
open CryptoVerification.SignalSession.Cli (
  CliInputsOk ElfStaticOk InputsLoadable MainCase MainEntryFacts MainGhost MainPost
  MainResult MuslHarness RunAllocFails RunAnswer argvAt cliInputs cliProg exit_frame
  fsView_congr fsView_writeAll_initFsState loadState_fs_trace mainName
  signExtend_ofNat_small
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)

/-! ## Entry Frame -/

/-- Entry separation-logic frame for `main` under `RustCliAllocBudget M`. -/
def mainFrame {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (stk : Nat) (Statics : SepProp) (i : Inputs) (s : State) : SepProp :=
  argvAt (s.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
    stackAt s.sp stk ∗ A.pool lim st s ∗ Statics

theorem mainFrame_symtab {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (stk : Nat) (Statics : SepProp) (i : Inputs) (s : State)
    (t : String → String → Option (BitVec 64)) :
    mainFrame A lim st stk Statics i { s with symtab := t } =
      mainFrame A lim st stk Statics i s := by
  unfold mainFrame
  have hpool : A.pool lim st { s with symtab := t } = A.pool lim st s :=
    A.pool_transport lim st s _ ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  rw [hpool]
  rfl

def mainEntryPre {M : AllocCostModel} (img : Obj.Image) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (stk : Nat) (Statics : SepProp)
    (i : Inputs) (s : State) : SepProp :=
  ⌜img.FrozenLoaded s ∧ stk ≤ s.sp.toNat⌝ ∗ mainFrame A lim st stk Statics i s

/-! ## Budget-Threaded `mainSpec` and `mainSpecTight` -/

/-- Budget-threaded `main` contract (`Spec (MainGhost × M.σ)`). -/
def mainSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (img : Obj.Image) (stk : Nat) (Statics : SepProp)
    (Run : Inputs → RunAnswer → Prop) : Spec (MainGhost × M.σ) :=
  Spec.inImage
    { pre := fun (g, st) s =>
        ⌜MainCase Run g.i g.r ∧ CliInputsOk g.i ∧ MainEntryFacts g.i s ∧
          stk ≤ s.sp.toNat⌝ ∗
          mainFrame A lim st stk Statics g.i s
      post := fun (g, _) s0 sf =>
        ⌜MainPost g.r s0 sf ∨ allocFailedIn s0 sf⌝ ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun (g, _) s0 sf =>
        ⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap
      onExit := fun _ _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap
      onOom := fun _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap }
    img

def mainSpecAt {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (img : Obj.Image) (stk : Nat) (Statics : SepProp)
    (Run : Inputs → RunAnswer → Prop) : Spec MainGhost :=
  Spec.inImage
    { pre := fun g s =>
        ⌜MainCase Run g.i g.r ∧ CliInputsOk g.i ∧ MainEntryFacts g.i s ∧
          stk ≤ s.sp.toNat⌝ ∗
          mainFrame A lim st stk Statics g.i s
      post := fun g s0 sf =>
        ⌜MainPost g.r s0 sf ∨ allocFailedIn s0 sf⌝ ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun g s0 sf =>
        ⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap
      onExit := fun _ _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap
      onOom := fun _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap }
    img

/-- Budget-threaded tightened `main` contract (`Spec (MainGhost × M.σ)`) where allocation failure routes exclusively to `onPanic`. -/
def mainSpecTight {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (img : Obj.Image) (stk : Nat) (Statics : SepProp)
    (Run : Inputs → RunAnswer → Prop) : Spec (MainGhost × M.σ) :=
  Spec.inImage
    { pre := fun (g, st) s =>
        ⌜MainCase Run g.i g.r ∧ CliInputsOk g.i ∧ MainEntryFacts g.i s ∧
          stk ≤ s.sp.toNat⌝ ∗
          mainFrame A lim st stk Statics g.i s
      post := fun (g, _) s0 sf =>
        ⌜MainPost g.r s0 sf⌝ ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun (g, _) s0 sf =>
        ⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap
      onExit := fun _ _ _ _ => ⌜False⌝
      onOom := fun _ _ _ => ⌜False⌝ }
    img

def mainSpecTightAt {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (img : Obj.Image) (stk : Nat) (Statics : SepProp)
    (Run : Inputs → RunAnswer → Prop) : Spec MainGhost :=
  Spec.inImage
    { pre := fun g s =>
        ⌜MainCase Run g.i g.r ∧ CliInputsOk g.i ∧ MainEntryFacts g.i s ∧
          stk ≤ s.sp.toNat⌝ ∗
          mainFrame A lim st stk Statics g.i s
      post := fun g s0 sf =>
        ⌜MainPost g.r s0 sf⌝ ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun g s0 sf =>
        ⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap
      onExit := fun _ _ _ _ => ⌜False⌝
      onOom := fun _ _ _ => ⌜False⌝ }
    img

theorem subroutine_ok_mainSpec_of_tight {P : Program} {e : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {img : Obj.Image} {stk : Nat} {Statics : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (h : subroutine_ok P e (mainSpecTight A lim img stk Statics Run)) :
    subroutine_ok P e (mainSpec A lim img stk Statics Run) := by
  refine subroutine_ok_mono h
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hp => ?_)
    (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ _ he => (not_satisfies_false_sepConj he).elim)
    (fun _ _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
  simp only [mainSpecTight, mainSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
  exact ⟨Or.inl hp.1, hp.2⟩

theorem subroutine_ok_mainSpecAt_of_mainSpec {P : Program} {e : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} (st : M.σ)
    {img : Obj.Image} {stk : Nat} {Statics : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (h : subroutine_ok P e (mainSpec A lim img stk Statics Run)) :
    subroutine_ok P e (mainSpecAt A lim st img stk Statics Run) :=
  subroutine_ok.of_codeLoaded fun g R s0 hpc hrun hpre hal _ =>
    h.mono_outcome (g, st) R s0 hpc hrun hpre hal fun _ hout => hout

theorem subroutine_ok_mainSpecTightAt_of_mainSpecTight {P : Program} {e : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} (st : M.σ)
    {img : Obj.Image} {stk : Nat} {Statics : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (h : subroutine_ok P e (mainSpecTight A lim img stk Statics Run)) :
    subroutine_ok P e (mainSpecTightAt A lim st img stk Statics Run) :=
  subroutine_ok.of_codeLoaded fun g R s0 hpc hrun hpre hal _ =>
    h.mono_outcome (g, st) R s0 hpc hrun hpre hal fun _ hout => hout

/-! ## Process Composition -/

/-- Composes `MuslHarness`, `SymtabGhost`, and budget-threaded `mainSpec`. -/
theorem outcome_of_main {elf : ElfImage} {img : Obj.Image} {ext : String → Option (State → State)}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {stk : Nat} {Statics Fr : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hE : ElfStaticOk elf)
    (hH : MuslHarness elf (cliProg img ext) (entryOf img mainName) Fr
      (fun i => CliInputsOk i ∧ InputsLoadable i) (mainEntryPre img A lim st stk Statics))
    (hG : SymtabGhost (cliProg img ext))
    (hmain : subroutine_ok (cliProg img ext) (entryOf img mainName)
      (mainSpec A lim img stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCase Run i r) :
    (∃ res, outcomeOf elf (cliProg img ext) (cliInputs i) = some res ∧
      MainResult.Observed i.files r res) ∨
    RunAllocFails elf (cliProg img ext) i := by
  obtain ⟨s0, sm, hload, hsteps0, hpc, hrun, hal, hfs, htr, hx0, hmem, hexit⟩ := hH hE i ⟨hi, hl⟩
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  simp only [mainEntryPre, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hFL, hsp⟩, hmem⟩ := hmem
  let sm' : State := { sm with symtab := img.symtab }
  have hpre : sm'.mem ⊨ (mainSpec A lim img stk Statics Run).pre (⟨i, r⟩, st) sm' ∗ Fr := by
    simp only [mainSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    have hentry : MainEntryFacts i sm' := by
      unfold MainEntryFacts; exact ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩
    have hfr : mainFrame A lim st stk Statics i sm' = mainFrame A lim st stk Statics i sm :=
      mainFrame_symtab A lim st stk Statics i sm img.symtab
    rw [hfr]
    exact ⟨⟨hFL.of_mem_eq rfl, rfl⟩, ⟨hc, hi, hentry, hsp⟩, hmem⟩
  have hcode : (cliProg img ext).CodeLoaded sm'.mem := hFL.codeLoaded_ofImage _ _
  obtain ⟨sf', hsteps1', hout, _⟩ :=
    hmain.no_fault_before_outcome (⟨i, r⟩, st) Fr sm' hpc hrun hpre hal hcode
  let sf : State := { sf' with symtab := sm.symtab }
  have hsteps1 : Steps (cliProg img ext) sm sf := by
    have h := hG sm.symtab hsteps1'
    exact h
  have hsteps01 := hsteps0.trans hsteps1
  have hAF : allocFailedIn sm' sf' → RunAllocFails elf (cliProg img ext) i :=
    fun h => ⟨s0, sf, hload, hsteps01, List.mem_of_mem_drop h⟩
  rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · simp only [mainSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hφ, hpost⟩ := hpost
    rcases hφ with ⟨code, w, out, rfl, hw0, hfiles, hout⟩ | hA
    · rw [← sepConj_assoc] at hpost
      have hret' : Returned sm sf := hret
      obtain ⟨sx, hsteps2, hst, hfsx, htrx⟩ :=
        hexit sf hsteps1 hret' (exit_frame hstk hstk' hpost)
      have hle := hc.code_le rfl
      have hw0' : (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code := hw0
      have hfiles' : sf.fs.files = (MainPost.writeAll sm'.fs w).files := hfiles
      have hout' : ProcessOutcome.traceStreamBytes .stdout sf.trace = out := hout
      refine Or.inl ⟨_, outcomeOf_eq_exited hload (hsteps01.trans hsteps2) hst, ?_⟩
      dsimp only [MainResult.Observed]
      refine ⟨?_, ?_, ?_⟩
      · rw [hw0', signExtend_ofNat_small hle]
      · rw [htrx, hout']
      · rw [hfsx, fsView_congr hfiles']
        change fsView (MainPost.writeAll sm.fs w) = _
        rw [hfs, hfs0]
        exact fsView_writeAll_initFsState i w hc.commitOk
    · exact Or.inr (hAF hA)
  · simp only [mainSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hpan' : sf.status = .Panicked := hpan
    rcases hpost.1 with rfl | hA
    · exact Or.inl ⟨_, outcomeOf_eq_aborted hload hsteps01 hpan', trivial⟩
    · exact Or.inr (hAF hA)
  · simp only [mainSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact Or.inr (hAF hpost.1)
  · simp only [mainSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact Or.inr (hAF hpost.1)

/-- Specialization of `outcome_of_main` to `cliExterns W`. -/
theorem outcome_of_main_cliExterns {elf : ElfImage} {img : Obj.Image} {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {stk : Nat} {Statics Fr : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hE : ElfStaticOk elf)
    (hH : MuslHarness elf (cliProg img (cliExterns W)) (entryOf img mainName) Fr
      (fun i => CliInputsOk i ∧ InputsLoadable i) (mainEntryPre img A lim st stk Statics))
    (hmain : subroutine_ok (cliProg img (cliExterns W)) (entryOf img mainName)
      (mainSpec A lim img stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCase Run i r) :
    (∃ res, outcomeOf elf (cliProg img (cliExterns W)) (cliInputs i) = some res ∧
      MainResult.Observed i.files r res) ∨
    RunAllocFails elf (cliProg img (cliExterns W)) i :=
  outcome_of_main hE hH (symtabGhost_ofImage_cliExterns img W) hmain hstk hstk' hi hl hc

/-- Unconditional OOM-disjunction process composition from budget-threaded `mainSpecTight`. -/
theorem outcome_of_main_or_oom {elf : ElfImage} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {stk : Nat} {Statics Fr : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hE : ElfStaticOk elf)
    (hH : MuslHarness elf (cliProg img ext) (entryOf img mainName) Fr
      (fun i => CliInputsOk i ∧ InputsLoadable i) (mainEntryPre img A lim st stk Statics))
    (hG : SymtabGhost (cliProg img ext))
    (hmain : subroutine_ok (cliProg img ext) (entryOf img mainName)
      (mainSpecTight A lim img stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCase Run i r) :
    (∃ res, outcomeOf elf (cliProg img ext) (cliInputs i) = some res ∧
      MainResult.Observed i.files r res) ∨
    (outcomeOf elf (cliProg img ext) (cliInputs i) = some .aborted ∧
      RunAllocFails elf (cliProg img ext) i) := by
  obtain ⟨s0, sm, hload, hsteps0, hpc, hrun, hal, hfs, htr, hx0, hmem, hexit⟩ := hH hE i ⟨hi, hl⟩
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  simp only [mainEntryPre, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hFL, hsp⟩, hmem⟩ := hmem
  let sm' : State := { sm with symtab := img.symtab }
  have hpre : sm'.mem ⊨ (mainSpecTight A lim img stk Statics Run).pre (⟨i, r⟩, st) sm' ∗ Fr := by
    simp only [mainSpecTight, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    have hentry : MainEntryFacts i sm' := by
      unfold MainEntryFacts; exact ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩
    have hfr : mainFrame A lim st stk Statics i sm' = mainFrame A lim st stk Statics i sm :=
      mainFrame_symtab A lim st stk Statics i sm img.symtab
    rw [hfr]
    exact ⟨⟨hFL.of_mem_eq rfl, rfl⟩, ⟨hc, hi, hentry, hsp⟩, hmem⟩
  have hcode : (cliProg img ext).CodeLoaded sm'.mem := hFL.codeLoaded_ofImage _ _
  obtain ⟨sf', hsteps1', hout, _⟩ :=
    hmain.no_fault_before_outcome (⟨i, r⟩, st) Fr sm' hpc hrun hpre hal hcode
  let sf : State := { sf' with symtab := sm.symtab }
  have hsteps1 : Steps (cliProg img ext) sm sf := by
    have h := hG sm.symtab hsteps1'
    exact h
  have hsteps01 := hsteps0.trans hsteps1
  have hAF : allocFailedIn sm' sf' → RunAllocFails elf (cliProg img ext) i :=
    fun h => ⟨s0, sf, hload, hsteps01, List.mem_of_mem_drop h⟩
  rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · simp only [mainSpecTight, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨code, w, out, rfl, hw0, hfiles, hout⟩, hpost⟩ := hpost
    rw [← sepConj_assoc] at hpost
    have hret' : Returned sm sf := hret
    obtain ⟨sx, hsteps2, hst, hfsx, htrx⟩ :=
      hexit sf hsteps1 hret' (exit_frame hstk hstk' hpost)
    have hle := hc.code_le rfl
    have hw0' : (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code := hw0
    have hfiles' : sf.fs.files = (MainPost.writeAll sm'.fs w).files := hfiles
    have hout' : ProcessOutcome.traceStreamBytes .stdout sf.trace = out := hout
    refine Or.inl ⟨_, outcomeOf_eq_exited hload (hsteps01.trans hsteps2) hst, ?_⟩
    dsimp only [MainResult.Observed]
    refine ⟨?_, ?_, ?_⟩
    · rw [hw0', signExtend_ofNat_small hle]
    · rw [htrx, hout']
    · rw [hfsx, fsView_congr hfiles']
      change fsView (MainPost.writeAll sm.fs w) = _
      rw [hfs, hfs0]
      exact fsView_writeAll_initFsState i w hc.commitOk
  · simp only [mainSpecTight, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hpan' : sf.status = .Panicked := hpan
    have habort := outcomeOf_eq_aborted hload hsteps01 hpan'
    rcases hpost.1 with rfl | hA
    · exact Or.inl ⟨_, habort, trivial⟩
    · exact Or.inr ⟨habort, hAF hA⟩
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-- Specialization of `outcome_of_main_or_oom` to `cliExterns W`. -/
theorem outcome_of_main_cliExterns_or_oom {elf : ElfImage} {img : Obj.Image} {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {stk : Nat} {Statics Fr : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hE : ElfStaticOk elf)
    (hH : MuslHarness elf (cliProg img (cliExterns W)) (entryOf img mainName) Fr
      (fun i => CliInputsOk i ∧ InputsLoadable i) (mainEntryPre img A lim st stk Statics))
    (hmain : subroutine_ok (cliProg img (cliExterns W)) (entryOf img mainName)
      (mainSpecTight A lim img stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCase Run i r) :
    (∃ res, outcomeOf elf (cliProg img (cliExterns W)) (cliInputs i) = some res ∧
      MainResult.Observed i.files r res) ∨
    (outcomeOf elf (cliProg img (cliExterns W)) (cliInputs i) = some .aborted ∧
      RunAllocFails elf (cliProg img (cliExterns W)) i) :=
  outcome_of_main_or_oom hE hH (symtabGhost_ofImage_cliExterns img W) hmain hstk hstk' hi hl hc

end LibsignalBinary.Proofs.SignalSession.Cli.Main.TopBudget
