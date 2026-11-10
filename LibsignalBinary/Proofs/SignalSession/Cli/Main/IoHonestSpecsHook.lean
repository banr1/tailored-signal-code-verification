/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Model -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced

/-!
# Exact-Hook → Honest-Spec Bridges for `write_file` and `write_stdout`
(`LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecsHook`)

- **Role**: `Role::Proof` (outside the TCB). Untrusted groundwork for #1255 (HOOKS-PREP).
- **Overview**:
  Proves that the idealized hooks `CliRun.writeFileHook` and `CliRun.writeStdoutHook` satisfy the
  honest contracts `writeFileHonestCore` / `writeFileSpecPlacedSat` and
  `writeStdoutHonestCore` / `writeStdoutSpecPlacedSat` (`IoHonestSpecs.lean`), so `HookSat`-backed
  sibling carriers can be instantiated from today's concrete hook table.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecsHook

open Arm64 Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks)
open CryptoVerification.RustHeap (allocFailedEvent)
open CryptoVerification.SignalSession
  (blockingAncestor? lsWriteFileSym lsWriteStdoutSym readPath writeFileHook writeStdoutHook)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunGlue (writeFileHook_fsT)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (hookSat_withVmPreserved vmPreserved_writeFileHook vmPreserved_writeStdoutHook)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced
  (writeFileHook_ok_placed writeStdoutHook_ok_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
  (writeFileHonestCore writeFileSpecPlacedSat writeStdoutHonestCore writeStdoutSpecPlacedSat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (writeFileSpecPlaced writeStdoutSpecPlaced)

private theorem writeFileHook_fds_eq (s : State) : (writeFileHook s).fs.fds = s.fs.fds := by
  unfold writeFileHook
  dsimp only []
  split_ifs
  · rfl
  · rfl
  · rfl
  · have hs1 :
        (s.appendTrace [.fileChanged (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1))]).fs.fds =
          s.fs.fds := rfl
    generalize s.appendTrace [.fileChanged (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1))] =
      s1 at hs1 ⊢
    cases blockingAncestor? s1.fs (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1)) with
    | some _ => exact hs1
    | none =>
      cases s1.fs.files (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1)) with
      | none => exact hs1
      | some entry => cases entry <;> exact hs1

private theorem writeFileHook_preserves_noAllocFailed (s : State)
    (h : allocFailedEvent ∉ s.trace) : allocFailedEvent ∉ (writeFileHook s).trace := by
  unfold writeFileHook
  dsimp only []
  split_ifs
  · exact h
  · exact h
  · exact h
  · have h1 : allocFailedEvent ∉
        (s.appendTrace [.fileChanged (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1))]).trace := by
      intro hm
      rcases List.mem_append.mp hm with hm0 | hm1
      · exact h hm0
      · simp [allocFailedEvent] at hm1
    generalize s.appendTrace [.fileChanged (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1))] =
      s1 at h1 ⊢
    cases blockingAncestor? s1.fs (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1)) with
    | some _ => exact h1
    | none =>
      cases s1.fs.files (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1)) with
      | none => exact h1
      | some entry => cases entry <;> exact h1

/-- The idealized `writeFileHook` meets the honest core contract `writeFileHonestCore`. -/
theorem writeFileHook_ok_honestCore {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) :
    HookOk writeFileHook (writeFileHonestCore cliIo A lim stk) := by
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ (writeFileSpecPlaced cliIo A lim stk).pre (x, st) s0 ∗ R := by
    simp only [writeFileHonestCore, writeFileSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
      at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk, hfits, _, _, _⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk, hfits⟩, hmem⟩
  rcases writeFileHook_ok_placed A lim stk (x, st) R s0 hrun hpre' hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcs, ?_⟩
    simp only [writeFileSpecPlaced, sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    simp only [writeFileHonestCore, sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨henv, hwr, htr, hstd⟩, hmem⟩
    exact ⟨⟨henv, hwr, htr, hstd, writeFileHook_fds_eq s0, writeFileHook_fsT s0,
      writeFileHook_preserves_noAllocFailed s0⟩, hmem⟩
  · exact Or.inr hrest

/-- The idealized `writeStdoutHook` meets the honest core contract `writeStdoutHonestCore`. -/
theorem writeStdoutHook_ok_honestCore {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) :
    HookOk writeStdoutHook (writeStdoutHonestCore A lim stk) := by
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  have hpre0 := hpre
  simp only [writeStdoutHonestCore, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hfits, _, _⟩, hmem0⟩
  obtain ⟨hlen, hrd⟩ := (IsBlock.pointsToBytes x.buf x.bs).read hmem0
  have hcan := (IsBlock.pointsToBytes x.buf x.bs).canRead hlen hmem0
  have heq : writeStdoutHook s0 =
      CryptoVerification.SignalSession.unitResult true
        (s0.appendTrace (TraceEvent.ofBytes .stdout x.bs)) := by
    unfold writeStdoutHook
    dsimp only []
    rw [hx0, hx1]
    simp only [hcan, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hrd]
  have hpre' : s0.mem ⊨ (writeStdoutSpecPlaced A lim stk).pre (x, st) s0 ∗ R := by
    simp only [writeStdoutSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hfits⟩, hmem0⟩
  rcases writeStdoutHook_ok_placed A lim stk (x, st) R s0 hrun hpre' hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcs, ?_⟩
    simp only [writeStdoutSpecPlaced, sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    simp only [writeStdoutHonestCore, sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨henv, hr0, hfiles, htr, hstd⟩, hmem⟩
    refine ⟨⟨henv, hr0, hfiles, htr, hstd, ?_, ?_⟩, hmem⟩
    · rw [heq]; rfl
    · rw [heq]; rfl
  · exact Or.inr hrest

/-- Exact-hook → `HookSat` bridge for `writeFileSpecPlacedSat` at `lsWriteFileSym`. -/
theorem hookSat_writeFileSpecPlacedSat_of_hook {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat} {H : LibsignalHooks}
    (h : H lsWriteFileSym = some writeFileHook) :
    HookSat H lsWriteFileSym (writeFileSpecPlacedSat cliIo A lim stk) :=
  hookSat_withVmPreserved ⟨writeFileHook, h, writeFileHook_ok_honestCore A lim stk⟩
    (fun f hf s => by cases h.symm.trans hf; exact vmPreserved_writeFileHook s)

/-- Exact-hook → `HookSat` bridge for `writeStdoutSpecPlacedSat` at `lsWriteStdoutSym`. -/
theorem hookSat_writeStdoutSpecPlacedSat_of_hook {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat} {H : LibsignalHooks}
    (h : H lsWriteStdoutSym = some writeStdoutHook) :
    HookSat H lsWriteStdoutSym (writeStdoutSpecPlacedSat A lim stk) :=
  hookSat_withVmPreserved ⟨writeStdoutHook, h, writeStdoutHook_ok_honestCore A lim stk⟩
    (fun f hf s => by cases h.symm.trans hf; exact vmPreserved_writeStdoutHook s)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecsHook
