/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryFixed
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.PqDirNoMatch
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqFixed

@[expose] public section

set_option autoImplicit false

/-!
# PQXDH-Mode OOM-Excuse Equivalences and Conditional Correctness

**Checked by Lean.** Equivalence and elimination lemmas relating the OOM-excused PQXDH
specifications (`OutcomeOrExcusedAbort`, `CliSpecPqxdhOrExcusedAbort`,
`CliSpecPqxdhNoMatchOrExcusedAbort`) to unconditional `CliSpecPqxdh` and `CliSpecPqxdhNoMatch`
when `CliReachesOOMPlaced` is excluded, together with fixed-image allocation-conditional
counterparts (`CliPqxdhAllocNeverFails`, `CliPqxdhElfCorrectUnderAllocOk`).
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

/-- Reaching `.OutOfMemory` (`CliReachesOOMPlaced mpl mmpl elf W i`) precludes `CliRunsToPlaced`
and forces `Placed.cliRunPlacedSig mpl mmpl elf W i = none`. -/
theorem cliRunPlacedSig_eq_none_of_reachesOOM
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks} {i : Inputs}
    (hOOM : CliReachesOOMPlaced mpl mmpl elf W i) :
    Placed.cliRunPlacedSig mpl mmpl elf W i = none := by
  rcases hOOM with ⟨s0, s, hload, hsteps, hoom⟩
  dsimp only [Placed.cliRunPlacedSig]
  split_ifs with h
  · exfalso
    rcases h with ⟨o, s0', hload', _, hsafe⟩
    cases hload.symm.trans hload'
    rcases hsafe s hsteps with ⟨_, (⟨_, hex, _⟩ | ⟨_, hsig, _⟩), _⟩ | ⟨_, hf⟩ | ⟨hrun, _⟩
    · cases hoom.symm.trans hex
    · cases hoom.symm.trans hsig
    · exact hf
    · cases hoom.symm.trans hrun
  · rfl

private theorem outcomeOrExcusedAbort_eq_of_not_exc {exc : Inputs → Prop} {run : CliRun}
    {i : Inputs} {e : Outcome} (h : OutcomeOrExcusedAbort exc run i (· = e)) (hn : ¬ exc i) :
    run i = some e := by
  rcases h with ⟨_, hr, rfl⟩ | ⟨_, hexc⟩
  · exact hr
  · exact (hn hexc).elim

private theorem outcomeOrExcusedAbort_false_eq_iff {run : CliRun} {i : Inputs} {e : Outcome} :
    OutcomeOrExcusedAbort (fun _ => False) run i (· = e) ↔ run i = some e := by
  unfold OutcomeOrExcusedAbort
  constructor
  · rintro (⟨_, hr, rfl⟩ | ⟨_, hf⟩)
    · exact hr
    · exact hf.elim
  · exact fun hr => .inl ⟨e, hr, rfl⟩

/-- At `exc := fun _ => False`, `CliSpecPqxdhOrExcusedAbort` is equivalent to `CliSpecPqxdh`. -/
theorem cliSpecPqxdhOrExcusedAbort_false_iff
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    CliSpecPqxdhOrExcusedAbort (fun _ => False) run X W ↔ CliSpecPqxdh run X W := by
  unfold CliSpecPqxdhOrExcusedAbort CliSpecPqxdh
  refine forall_congr' fun st => imp_congr_right fun _ => ?_
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · exact forall_congr' fun b => forall_congr' fun t => imp_congr_right fun _ =>
      outcomeOrExcusedAbort_false_eq_iff
  · exact forall_congr' fun m => forall_congr' fun r => imp_congr_right fun _ =>
      outcomeOrExcusedAbort_false_eq_iff.trans (by split_ifs <;> rfl)
  · exact forall_congr' fun c => forall_congr' fun rc => imp_congr_right fun _ =>
      outcomeOrExcusedAbort_false_eq_iff.trans (by split_ifs <;> rfl)
  · exact forall_congr' fun m => forall_congr' fun rc => imp_congr_right fun _ =>
      imp_congr_right fun _ =>
        outcomeOrExcusedAbort_false_eq_iff.trans (by split_ifs <;> rfl)
  · exact forall_congr' fun c => forall_congr' fun rc => imp_congr_right fun _ =>
      imp_congr_right fun _ => imp_congr_right fun _ =>
        outcomeOrExcusedAbort_false_eq_iff.trans (by split_ifs <;> rfl)

/-- At `exc := fun _ => False`, `CliSpecPqxdhNoMatchOrExcusedAbort` is equivalent to
`CliSpecPqxdhNoMatch`. -/
theorem cliSpecPqxdhNoMatchOrExcusedAbort_false_iff
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    CliSpecPqxdhNoMatchOrExcusedAbort (fun _ => False) run X W ↔ CliSpecPqxdhNoMatch run X W := by
  unfold CliSpecPqxdhNoMatchOrExcusedAbort CliSpecPqxdhNoMatch OutcomeOrExcusedAbort
  refine forall_congr' fun st => imp_congr_right fun _ => ?_
  refine forall_congr' fun x => forall_congr' fun g => imp_congr_right fun _ => ?_
  refine forall_congr' fun m => forall_congr' fun rc => imp_congr_right fun _ => ?_
  refine imp_congr_right fun _ => ?_
  by_cases hg : (wirePrekey :: m.bytes).length > stdinCapBytes
  · simp only [hg, ↓reduceIte, and_false, or_false]
    exact ⟨fun ⟨_, hr, he⟩ => he ▸ hr, fun hr => ⟨_, hr, rfl⟩⟩
  · simp only [hg, ↓reduceIte, and_false, or_false]

/-- Excluding `CliReachesOOMPlaced` across `CliPqxdhInputs` recovers `CliSpecPqxdh` from
`CliPqxdhElfCorrectPlaced`. -/
theorem cliSpecPqxdh_of_elfCorrectPlaced_and_noOOM
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    (hL4 : CliPqxdhElfCorrectPlaced mpl mmpl elf)
    (hNoOOM : ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    CliSpecPqxdh (Placed.cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ := by
  intro st hdom
  rcases (hL4.2 W X).1 st hdom with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    exact outcomeOrExcusedAbort_eq_of_not_exc (h1 b t hnone)
      (hNoOOM _ ⟨st, hdom, .inl ⟨hnone, b, t, rfl⟩⟩)
  · intro m r hlen
    have hr := outcomeOrExcusedAbort_eq_of_not_exc (h2 m r hlen)
      (hNoOOM _ ⟨st, hdom, .inr (.inl ⟨m, r, hlen, rfl⟩)⟩)
    split_ifs at hr ⊢ <;> exact hr
  · intro c rc hlen
    have hr := outcomeOrExcusedAbort_eq_of_not_exc (h3 c rc hlen)
      (hNoOOM _ ⟨st, hdom, .inr (.inr (.inl ⟨c, rc, hlen, rfl⟩))⟩)
    split_ifs at hr ⊢ <;> exact hr
  · intro m rc hlen hmatch
    have hr := outcomeOrExcusedAbort_eq_of_not_exc (h4 m rc hlen hmatch)
      (hNoOOM _ ⟨st, hdom, .inr (.inr (.inr (.inl ⟨m, rc, hlen, rfl⟩)))⟩)
    split_ifs at hr ⊢ <;> exact hr
  · intro c rc hlen hw hp
    have hr := outcomeOrExcusedAbort_eq_of_not_exc (h5 c rc hlen hw hp)
      (hNoOOM _ ⟨st, hdom, .inr (.inr (.inr (.inr ⟨c, rc, hlen, hw, hp, rfl⟩)))⟩)
    split_ifs at hr ⊢ <;> exact hr

/-- Excluding `CliReachesOOMPlaced` across `CliPqxdhInputs` recovers `CliSpecPqxdhNoMatch` from
`CliPqxdhElfCorrectPlaced`. -/
theorem cliSpecPqxdhNoMatch_of_elfCorrectPlaced_and_noOOM
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    (hL4 : CliPqxdhElfCorrectPlaced mpl mmpl elf)
    (hNoOOM : ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    CliSpecPqxdhNoMatch (Placed.cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ := by
  intro st hdom x g hsess m rc hlen hnomatch
  have h := (hL4.2 W X).2 st hdom x g hsess m rc hlen hnomatch
  have hn := hNoOOM _ ⟨st, hdom, .inr (.inr (.inr (.inl ⟨m, rc, hlen, rfl⟩)))⟩
  rcases h with ⟨o, hr, ho⟩ | ⟨_, hexc⟩
  · by_cases hg : (wirePrekey :: m.bytes).length > stdinCapBytes
    · simp only [hg, ↓reduceIte] at ho ⊢
      exact ho ▸ hr
    · simp only [hg, ↓reduceIte] at ho ⊢
      exact ⟨o, hr, ho⟩
  · exact (hn hexc).elim

/-- On every input in `CliPqxdhInputs ⟨W.C, W.Q⟩`, no state reached from `cliTokenPatch s0` under
`cliProgAbortOnPanic W` logs `allocFailedEvent`. -/
def CliPqxdhAllocNeverFails (elf : ElfImage) (W : CliHooks) : Prop :=
  ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
    ∀ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliProgAbortOnPanic W) (cliTokenPatch s0) s → RustHeap.allocFailedEvent ∉ s.trace

/-- Fixed-image PQXDH correctness of `elf` conditioned on `CliPqxdhAllocNeverFails elf W`. -/
def CliPqxdhElfCorrectUnderAllocOk (elf : ElfImage) : Prop :=
  CliElfCodeMatches elf ∧
  ∀ W : CliHooks, CliPqxdhAllocNeverFails elf W →
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩ ∧
      CliSpecPqxdhNoMatch (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩

/-- Bytes-level counterpart of `CliPqxdhElfCorrectUnderAllocOk`. -/
def CliPqxdhBinaryCorrectUnderAllocOk (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqxdhElfCorrectUnderAllocOk elf

/-- Eliminates the per-hook `CliPqxdhAllocNeverFails` hypothesis from
`CliPqxdhElfCorrectUnderAllocOk`. -/
theorem CliPqxdhElfCorrectUnderAllocOk.toCliPqxdhElfCorrect {elf : ElfImage}
    (h : CliPqxdhElfCorrectUnderAllocOk elf)
    (hAlloc : ∀ W : CliHooks, CliPqxdhAllocNeverFails elf W) :
    CliPqxdhElfCorrect elf :=
  ⟨h.1, fun W X => h.2 W (hAlloc W) X⟩

/-- Some state reached by `elf` on `i` from `cliTokenPatch s0` under `cliProgAbortOnPanic W` logs
`allocFailedEvent`. -/
def cliRunHitsAllocFailure (elf : ElfImage) (W : CliHooks) (i : Inputs) : Prop :=
  ∃ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (cliProgAbortOnPanic W) (cliTokenPatch s0) s ∧ RustHeap.allocFailedEvent ∈ s.trace

end CryptoVerification.SignalSession
