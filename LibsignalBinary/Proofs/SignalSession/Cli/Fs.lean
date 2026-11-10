/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Fs
import ProofLib.Hoare.Safety
import ProofLib.VCGen

/-!
# File-System Invariant Across a CLI Run

The CLI writes files only in `Stores::commit`, after `run` returns, while every store callback
reads them through `Dir::get`. This module lifts `StoreKit/Fs.lean`'s trace-stability invariant
`FsInv F0 T0 s` to Hoare triples via `withFsInv spec F0 T0` and `subroutine_ok_withFsInv` so
`fs.files = F0` is carried across allocator, codec, and libsignal calls without modifying callee
specifications.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoVerification.LibsignalPublicApi.StoreKit

/-- `spec` with `⌜FsInv F0 T0 ·⌝` added to the precondition and to every outcome. -/
def withFsInv {α : Type} (spec : Spec α) (F0 : FsFiles) (T0 : List TraceEvent) : Spec α where
  pre x s := ⌜FsInv F0 T0 s⌝ ∗ spec.pre x s
  post x s0 sf := ⌜FsInv F0 T0 sf⌝ ∗ spec.post x s0 sf
  onPanic x s0 sf := ⌜FsInv F0 T0 sf⌝ ∗ spec.onPanic x s0 sf
  onExit x c s0 sf := ⌜FsInv F0 T0 sf⌝ ∗ spec.onExit x c s0 sf
  onOom x s0 sf := ⌜FsInv F0 T0 sf⌝ ∗ spec.onOom x s0 sf

/-- For a trace-sound program, every triple carries `FsInv` across the call. -/
theorem subroutine_ok_withFsInv {α : Type} {P : Program} {e : BitVec 64} {spec : Spec α}
    (hP : TraceFsSound P) (h : subroutine_ok P e spec) (F0 : FsFiles) (T0 : List TraceEvent) :
    subroutine_ok P e (withFsInv spec F0 T0) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hal hcode => ?_
  simp only [withFsInv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv, hpre⟩ := hpre
  obtain ⟨sf, hsteps, hout, -⟩ := h.no_fault_before_outcome x R s0 hpc hrun hpre hal hcode
  have hinv' := hinv.of_steps hP hsteps
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  simp only [SubroutineOutcome, withFsInv, sepConj_assoc, satisfies_pure_sepConj] at hout ⊢
  rcases hout with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨c, h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl ⟨h1, h2, hinv', h3⟩
  · exact .inr (.inl ⟨h1, hinv', h2⟩)
  · exact .inr (.inr (.inl ⟨c, h1, hinv', h2⟩))
  · exact .inr (.inr (.inr ⟨h1, hinv', h2⟩))

theorem withFsInv_pre_intro {α : Type} {spec : Spec α} {F0 : FsFiles} {T0 : List TraceEvent}
    {x : α} {s : State} {R : SepProp} (hinv : FsInv F0 T0 s) (h : s.mem ⊨ spec.pre x s ∗ R) :
    s.mem ⊨ (withFsInv spec F0 T0).pre x s ∗ R := by
  show s.mem ⊨ (⌜FsInv F0 T0 s⌝ ∗ spec.pre x s) ∗ R
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hinv, h⟩

theorem withFsInv_post_elim {α : Type} {spec : Spec α} {F0 : FsFiles} {T0 : List TraceEvent}
    {x : α} {s0 sf : State} {R : SepProp} (h : sf.mem ⊨ (withFsInv spec F0 T0).post x s0 sf ∗ R) :
    FsInv F0 T0 sf ∧ (sf.mem ⊨ spec.post x s0 sf ∗ R) := by
  change sf.mem ⊨ (⌜FsInv F0 T0 sf⌝ ∗ spec.post x s0 sf) ∗ R at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h

/-- At the entry of `main`, `FsInv` holds with the entry files and trace. -/
theorem withFsInv_entry (s : State) : FsInv s.fs.files s.trace s := FsInv.of_entry s

/-- At a store callback, a CLI kit's `envOk := (· = F0)` holds once the trace since `T0` is the
known quiet events `evs` (the CLI's kits add none; the coins hook adds `userDefined` events). -/
theorem files_eq_at_callback {F0 : FsFiles} {T0 : List TraceEvent} {s : State}
    (hinv : FsInv F0 T0 s) {evs : List TraceEvent} (ht : s.trace = T0 ++ evs)
    (hq : NoFsEv evs) : s.fs.files = F0 :=
  hinv.files_eq ht hq

/-- The CLI's Files kits (`envOk := (· = F0)`, no kit event) meet `KitFsOk` from trace soundness;
`Q` is the kits' quietness, `True` for the CLI. -/
theorem filesKit_fsOk {P : Program} (hP : TraceFsSound P) (F0 : FsFiles) :
    KitFsOk (· = F0) True P :=
  KitFsOk.of_sound trivial hP

end CryptoVerification.SignalSession.Cli
