/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq

/-!
# `¬ CliReachesOOMPlaced` Step-Safety and 6-Clause Totality Bridge

Discharges `¬ CliReachesOOMPlaced mpl mmpl elf W i` across `CliPqxdhInputs ⟨W.C, W.Q⟩ i` from
strict 2-placement PQXDH correctness (`CliSpecPqxdh` and `CliSpecPqxdhNoMatch`) via `ProcessRunsTo`
step safety (`oom := fun _ => False`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.L4A.T2NoOomBridge

open Arm64 Arm64.Obj Arm64.Process
open CryptoVerification.E2E (UnreachedPqxdhPrimitives wirePrekey wireWhisper)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs CliReachesOOMPlaced CliSpecPqxdh CliSpecPqxdhNoMatch Inputs Outcome
   PqSessionMatches maxPlaintextBytes stdinCapBytes)
open CryptoVerification.SignalSession.Placed
  (CliRunsToPlaced cliRunPlacedSig)

/-- Step-safety refutation: if `Placed.CliRunsToPlaced mpl mmpl elf W i o` holds, then
`ProcessRunsTo`'s step-safety clause (`oom := fun _ => False`) refutes `s.status = .OutOfMemory`
on every reachable state `s`. -/
theorem not_cliReachesOOMPlaced_of_cliRunsToPlaced
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks} {i : Inputs} {o : Outcome}
    (hr : CliRunsToPlaced mpl mmpl elf W i o) :
    ¬ CliReachesOOMPlaced mpl mmpl elf W i := by
  rcases hr with ⟨s0, hload, _, hsafe⟩
  rintro ⟨s0', s, hload', hsteps, hs⟩
  have hs0 : s0' = s0 := by
    rw [hload] at hload'
    cases hload'
    rfl
  subst hs0
  rcases hsafe s hsteps with ⟨_, hterm, _⟩ | ⟨_, hfalse⟩ | ⟨hrun, _⟩
  · rcases hterm with ⟨_, hex, _⟩ | ⟨_, hsig, _⟩
    · rw [hs] at hex; cases hex
    · rw [hs] at hsig; cases hsig
  · exact hfalse
  · rw [hs] at hrun; cases hrun

/-- Exact-outcome inversion: `Placed.cliRunPlacedSig mpl mmpl elf W i = some o` yields
`Placed.CliRunsToPlaced mpl mmpl elf W i o` for the same `o : Outcome`. -/
theorem cliRunsToPlaced_of_cliRunPlacedSig_eq_some
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks} {i : Inputs} {o : Outcome}
    (h : cliRunPlacedSig mpl mmpl elf W i = some o) :
    CliRunsToPlaced mpl mmpl elf W i o := by
  unfold cliRunPlacedSig at h
  split at h
  · rename_i hex
    injection h with ho
    exact ho ▸ Classical.choose_spec hex
  · cases h

/-- 6-clause totality: under `CliSpecPqxdh` and `CliSpecPqxdhNoMatch`, every `i` in
`CliPqxdhInputs ⟨W.C, W.Q⟩ i` produces `∃ o, cliRunPlacedSig mpl mmpl elf W i = some o`. -/
theorem exists_cliRunPlacedSig_of_cliPqxdhInputs
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks} {i : Inputs}
    (X : UnreachedPqxdhPrimitives)
    (hSpec : CliSpecPqxdh (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩)
    (hNoMatch : CliSpecPqxdhNoMatch (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    ∃ o : Outcome, cliRunPlacedSig mpl mmpl elf W i = some o := by
  rcases hi with ⟨st, hdom, hclause⟩
  obtain ⟨hInit, hSend, hWhisper, hPrekeyMatch, hOther⟩ := hSpec st hdom
  rcases hclause with
      ⟨hnone, b, t, rfl⟩ |
      ⟨m, r, hlen, rfl⟩ |
      ⟨c, rc, hlen, rfl⟩ |
      ⟨m, rc, hlen, rfl⟩ |
      ⟨c, rc, hlen, hhw, hhp, rfl⟩
  · exact ⟨_, hInit b t hnone⟩
  · have h := hSend m r hlen
    by_cases h1 : m.length > stdinCapBytes
    · simp only [h1, ↓reduceIte] at h
      exact ⟨_, h⟩
    · by_cases h2 : m.length > maxPlaintextBytes
      · simp only [h1, h2, ↓reduceIte] at h
        exact ⟨_, h⟩
      · simp only [h1, h2, ↓reduceIte] at h
        exact ⟨_, h⟩
  · have h := hWhisper c rc hlen
    by_cases h1 : (wireWhisper :: c).length > stdinCapBytes <;>
      simp only [h1, ↓reduceIte] at h <;>
      exact ⟨_, h⟩
  · cases hsess : st.session with
    | none =>
      have h := hPrekeyMatch m rc hlen (by intro _ _ h'; rw [hsess] at h'; cases h')
      by_cases h1 : (wirePrekey :: m.bytes).length > stdinCapBytes <;>
        simp only [h1, ↓reduceIte] at h <;>
        exact ⟨_, h⟩
    | some xg =>
      rcases xg with ⟨x, g⟩
      by_cases hm : PqSessionMatches x g m
      · have h := hPrekeyMatch m rc hlen (by
          intro x' g' h'
          rw [hsess] at h'
          injection h' with hpair
          cases hpair
          exact hm)
        by_cases h1 : (wirePrekey :: m.bytes).length > stdinCapBytes <;>
          simp only [h1, ↓reduceIte] at h <;>
          exact ⟨_, h⟩
      · have h := hNoMatch st hdom x g hsess m rc hlen hm
        by_cases h1 : (wirePrekey :: m.bytes).length > stdinCapBytes
        · simp only [h1, ↓reduceIte] at h
          exact ⟨_, h⟩
        · simp only [h1, ↓reduceIte] at h
          obtain ⟨o, ho, _⟩ := h
          exact ⟨o, ho⟩
  · have h := hOther c rc hlen hhw hhp
    by_cases h1 : c.length > stdinCapBytes <;>
      simp only [h1, ↓reduceIte] at h <;>
      exact ⟨_, h⟩

/-- Default witness for `UnreachedPqxdhPrimitives` used solely to instantiate universally
quantified strictness hypotheses (`CliReachesOOMPlaced` is independent of `X`). -/
private def defaultUnreachedPqxdhPrimitives : UnreachedPqxdhPrimitives where
  sigPkGen := fun _ => []
  sigSign := fun _ _ _ => []
  scalarMul := fun _ _ => []
  scalarAdd := fun _ _ => []
  kemKeyGen := fun _ => ([], [])
  pow8 := fun _ => []
  isValidDhTriple := fun _ _ _ => false

theorem not_cliReachesOOMPlaced_of_spec_and_noMatch
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks}
    (X : UnreachedPqxdhPrimitives)
    (hSpec : CliSpecPqxdh (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩)
    (hNoMatch : CliSpecPqxdhNoMatch (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩)
    (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    ¬ CliReachesOOMPlaced mpl mmpl elf W i := by
  obtain ⟨o, ho⟩ := exists_cliRunPlacedSig_of_cliPqxdhInputs X hSpec hNoMatch hi
  exact not_cliReachesOOMPlaced_of_cliRunsToPlaced
    (cliRunsToPlaced_of_cliRunPlacedSig_eq_some ho)

theorem not_cliReachesOOMPlaced_of_strict
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks}
    (hStrictW : ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ ∧
      CliSpecPqxdhNoMatch (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩)
    (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    ¬ CliReachesOOMPlaced mpl mmpl elf W i :=
  let ⟨hSpec, hNoMatch⟩ := hStrictW defaultUnreachedPqxdhPrimitives
  not_cliReachesOOMPlaced_of_spec_and_noMatch defaultUnreachedPqxdhPrimitives hSpec hNoMatch i hi

end LibsignalBinary.Proofs.SignalSession.Cli.F3.L4A.T2NoOomBridge
