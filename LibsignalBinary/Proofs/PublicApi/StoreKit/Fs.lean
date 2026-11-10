/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome
import ProofLib.BV.WidthNorm

/-!
# File-System Preservation Invariants for Store Callbacks

Kit-independent trace and file-system invariants (`QuietEv`, `NoFsEv`, `TraceFsSound`, `FsInv`,
`FsCtx`, `FsAt`) connecting `s.fs.files` at each store callback poll to the entry file-system
snapshot `s0.fs.files` whenever intervening trace events are file-system-quiet.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.StoreKit

open Arm64 ProofLib

/-- Type alias for the `fs.files` map of `State`. -/
abbrev FsFiles : Type := String → Option FsEntry

/-! ## Quiet Trace Events -/

/-- Decidable check for events that cannot mutate `fs.files` (`stdout`/`stderr` byte writes and
non-`"fs_write"` `userDefined` events). -/
def quietEv : TraceEvent → Bool
  | .writeByte .stdout _ => true
  | .writeByte .stderr _ => true
  | .userDefined tag _ => tag != "fs_write"
  | _ => false

/-- Predicate asserting that trace event `e` does not mutate `fs.files`. -/
def QuietEv (e : TraceEvent) : Prop := quietEv e = true

instance (e : TraceEvent) : Decidable (QuietEv e) :=
  inferInstanceAs (Decidable (quietEv e = true))

/-- Every trace event in `d` satisfies `QuietEv`. -/
def NoFsEv (d : List TraceEvent) : Prop := ∀ e ∈ d, QuietEv e

@[simp] theorem quietEv_stdout (b : BitVec 8) : quietEv (.writeByte .stdout b) = true := rfl
@[simp] theorem quietEv_stderr (b : BitVec 8) : quietEv (.writeByte .stderr b) = true := rfl
@[simp] theorem quietEv_fd (n : BitVec 64) (b : BitVec 8) :
    quietEv (.writeByte (.fd n) b) = false := rfl
@[simp] theorem quietEv_userDefined (tag : String) (p : List (BitVec 8)) :
    quietEv (.userDefined tag p) = (tag != "fs_write") := rfl

@[simp] theorem QuietEv.iff (e : TraceEvent) : QuietEv e ↔ quietEv e = true := Iff.rfl

@[simp] theorem NoFsEv.nil : NoFsEv [] := fun _ h => absurd h List.not_mem_nil

@[simp] theorem NoFsEv.cons_iff {e : TraceEvent} {d : List TraceEvent} :
    NoFsEv (e :: d) ↔ QuietEv e ∧ NoFsEv d := by
  simp [NoFsEv]

@[simp] theorem NoFsEv.append_iff {d₁ d₂ : List TraceEvent} :
    NoFsEv (d₁ ++ d₂) ↔ NoFsEv d₁ ∧ NoFsEv d₂ := by
  simp only [NoFsEv, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (.inl he), fun e he => h e (.inr he)⟩,
    fun ⟨h₁, h₂⟩ e he => he.elim (h₁ e) (h₂ e)⟩

theorem NoFsEv.append {d₁ d₂ : List TraceEvent} (h₁ : NoFsEv d₁) (h₂ : NoFsEv d₂) :
    NoFsEv (d₁ ++ d₂) :=
  NoFsEv.append_iff.2 ⟨h₁, h₂⟩

theorem NoFsEv.left {d₁ d₂ : List TraceEvent} (h : NoFsEv (d₁ ++ d₂)) : NoFsEv d₁ :=
  (NoFsEv.append_iff.1 h).1

theorem NoFsEv.right {d₁ d₂ : List TraceEvent} (h : NoFsEv (d₁ ++ d₂)) : NoFsEv d₂ :=
  (NoFsEv.append_iff.1 h).2

theorem NoFsEv.userDefined {tag : String} (p : List (BitVec 8)) (h : tag ≠ "fs_write") :
    NoFsEv [.userDefined tag p] := by
  simp [h]

@[simp] theorem NoFsEv.ofBytes_stdout (bs : List (BitVec 8)) :
    NoFsEv (TraceEvent.ofBytes .stdout bs) := by
  intro e he
  simp only [TraceEvent.ofBytes, List.mem_map] at he
  obtain ⟨b, -, rfl⟩ := he
  rfl

@[simp] theorem NoFsEv.ofBytes_stderr (bs : List (BitVec 8)) :
    NoFsEv (TraceEvent.ofBytes .stderr bs) := by
  intro e he
  simp only [TraceEvent.ofBytes, List.mem_map] at he
  obtain ⟨b, -, rfl⟩ := he
  rfl

theorem NoFsEv.not_isFs {isFs : TraceEvent → Prop} (hfs : ∀ e, isFs e → ¬ QuietEv e)
    {d : List TraceEvent} (h : NoFsEv d) : ∀ e ∈ d, ¬ isFs e :=
  fun e he hfe => hfs e hfe (h e he)

/-! ## Program File-System Trace Soundness -/

/-- Along every execution of `P`, the trace grows monotonically and `fs.files` is preserved
whenever all newly emitted events satisfy `NoFsEv`. -/
def TraceFsSound (P : Program) : Prop :=
  ∀ s s', Steps P s s' →
    ∃ d, s'.trace = s.trace ++ d ∧ (NoFsEv d → s'.fs.files = s.fs.files)

/-- Derives `TraceFsSound P` from any event predicate `isFs` that implies `¬ QuietEv`. -/
theorem TraceFsSound.of_isFs {P : Program} {isFs : TraceEvent → Prop}
    (hfs : ∀ e, isFs e → ¬ QuietEv e)
    (hM : ∀ s s', Steps P s s' →
      ∃ d, s'.trace = s.trace ++ d ∧ ((∀ e ∈ d, ¬ isFs e) → s'.fs.files = s.fs.files)) :
    TraceFsSound P := by
  intro s s' hst
  obtain ⟨d, htr, hf⟩ := hM s s' hst
  exact ⟨d, htr, fun hq => hf (hq.not_isFs hfs)⟩

/-- Under `TraceFsSound P`, reaching `s` from `s0` while emitting only `NoFsEv` events preserves
`fs.files`. -/
theorem TraceFsSound.files_eq {P : Program} (hP : TraceFsSound P) {s0 s : State}
    (hreach : Steps P s0 s) {evs : List TraceEvent} (htr : s.trace = s0.trace ++ evs)
    (hq : NoFsEv evs) : s.fs.files = s0.fs.files := by
  obtain ⟨d, htr', hf⟩ := hP s0 s hreach
  have hd : d = evs := List.append_cancel_left (htr'.symm.trans htr)
  subst hd
  exact hf hq

/-! ## `FsInv` -/

/-- Trace-indexed file-system invariant: `s.trace` extends `T0` by `e`, and `NoFsEv e` implies
`s.fs.files = F0`. -/
def FsInv (F0 : FsFiles) (T0 : List TraceEvent) (s : State) : Prop :=
  ∃ e, s.trace = T0 ++ e ∧ (NoFsEv e → s.fs.files = F0)

theorem FsInv.of_entry (s : State) : FsInv s.fs.files s.trace s :=
  ⟨[], (List.append_nil _).symm, fun _ => rfl⟩

theorem FsInv.files_eq {F0 : FsFiles} {T0 : List TraceEvent} {s : State}
    (h : FsInv F0 T0 s) {evs : List TraceEvent} (ht : s.trace = T0 ++ evs) (hq : NoFsEv evs) :
    s.fs.files = F0 := by
  obtain ⟨e, he, hf⟩ := h
  have : e = evs := List.append_cancel_left (he.symm.trans ht)
  subst this
  exact hf hq

/-- `FsInv` is preserved across `Steps P` when `TraceFsSound P` holds. -/
theorem FsInv.of_steps {P : Program} (hP : TraceFsSound P) {F0 : FsFiles}
    {T0 : List TraceEvent} {s s' : State} (h : FsInv F0 T0 s) (hst : Steps P s s') :
    FsInv F0 T0 s' := by
  obtain ⟨e, he, hf⟩ := h
  obtain ⟨d, hd, hfd⟩ := hP s s' hst
  refine ⟨e ++ d, by rw [hd, he, List.append_assoc], fun hq => ?_⟩
  rw [hfd hq.right]
  exact hf hq.left

/-- Stability of `FsInv F0 T0` across all `Steps P` executions. -/
def CliFsSound (P : Program) : Prop :=
  ∀ F0 T0 s s', FsInv F0 T0 s → Steps P s s' → FsInv F0 T0 s'

theorem TraceFsSound.cliFsSound {P : Program} (hP : TraceFsSound P) : CliFsSound P :=
  fun _ _ _ _ h hst => h.of_steps hP hst

/-! ## Re-Establishing `envOk` at Store Callbacks -/

/-- Sufficient condition for re-establishing `envOk` at store callbacks: either `envOk` is
trivial, or kit events satisfy `Q` and `TraceFsSound P` holds. -/
def KitFsOk (envOk : FsFiles → Prop) (Q : Prop) (P : Program) : Prop :=
  (∀ f, envOk f) ∨ (Q ∧ TraceFsSound P)

theorem KitFsOk.of_true {Q : Prop} {P : Program} : KitFsOk (fun _ => True) Q P :=
  .inl fun _ => trivial

theorem KitFsOk.of_sound {envOk : FsFiles → Prop} {Q : Prop} {P : Program} (hQ : Q)
    (hP : TraceFsSound P) : KitFsOk envOk Q P := .inr ⟨hQ, hP⟩

/-- Entry-to-current file-system context threaded across multi-segment `Steps P` proofs. -/
def FsCtx (envOk : FsFiles → Prop) (Q : Prop) (P : Program) (s0 s : State) : Prop :=
  (∀ f, envOk f) ∨ (Q ∧ TraceFsSound P ∧ envOk s0.fs.files ∧ Steps P s0 s)

theorem FsCtx.of_entry {envOk : FsFiles → Prop} {Q : Prop} {P : Program} {s0 : State}
    (h : KitFsOk envOk Q P) (h0 : envOk s0.fs.files) : FsCtx envOk Q P s0 s0 := by
  rcases h with h | ⟨hQ, hP⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, h0, Steps.refl s0⟩

theorem FsCtx.of_steps {envOk : FsFiles → Prop} {Q : Prop} {P : Program} {s0 s s' : State}
    (h : FsCtx envOk Q P s0 s) (hst : Steps P s s') : FsCtx envOk Q P s0 s' := by
  rcases h with h | ⟨hQ, hP, h0, hr⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, h0, hr.trans hst⟩

/-- Extracts `envOk s.fs.files` from `FsCtx` when the trace delta `evs` since `s0` is quiet
under `Q`. -/
theorem FsCtx.envOk_at {envOk : FsFiles → Prop} {Q : Prop} {P : Program} {s0 s : State}
    (h : FsCtx envOk Q P s0 s) {evs : List TraceEvent} (htr : s.trace = s0.trace ++ evs)
    (hq : Q → NoFsEv evs) : envOk s.fs.files := by
  rcases h with h | ⟨hQ, hP, h0, hr⟩
  · exact h _
  · rw [hP.files_eq hr htr (hq hQ)]
    exact h0

/-- Re-anchors `FsCtx` at `s` once the trace delta since `s0` is known to be quiet. -/
theorem FsCtx.rebase {envOk : FsFiles → Prop} {Q : Prop} {P : Program} {s0 s : State}
    (h : FsCtx envOk Q P s0 s) {evs : List TraceEvent} (htr : s.trace = s0.trace ++ evs)
    (hq : Q → NoFsEv evs) : FsCtx envOk Q P s s := by
  have he := h.envOk_at htr hq
  rcases h with h | ⟨hQ, hP, -, -⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, he, Steps.refl s⟩

theorem FsCtx.mono {e₁ e₂ : FsFiles → Prop} {Q₁ Q₂ : Prop} {P : Program} {s0 s : State}
    (he : ∀ f, e₁ f → e₂ f) (hQ : Q₁ → Q₂) (h : FsCtx e₁ Q₁ P s0 s) : FsCtx e₂ Q₂ P s0 s := by
  rcases h with h | ⟨hq, hP, h0, hr⟩
  · exact .inl fun f => he f (h f)
  · exact .inr ⟨hQ hq, hP, he _ h0, hr⟩

/-! ## Pointwise `SepWP` File-System Carrier (`FsAt`) -/

/-- Pointwise counterpart of `FsCtx` at a single state `s`, suitable for threading through
`SepWP` proofs without referencing an entry state `s0`. -/
def FsAt (envOk : FsFiles → Prop) (Q : Prop) (P : Program) (s : State) : Prop :=
  (∀ f, envOk f) ∨ (Q ∧ TraceFsSound P ∧ envOk s.fs.files)

theorem FsAt.envOk_here {envOk : FsFiles → Prop} {Q : Prop} {P : Program} {s : State}
    (h : FsAt envOk Q P s) : envOk s.fs.files := by
  rcases h with h | ⟨-, -, h⟩
  · exact h _
  · exact h

theorem FsAt.of_files_eq {envOk : FsFiles → Prop} {Q : Prop} {P : Program} {s s' : State}
    (h : FsAt envOk Q P s) (hf : s'.fs.files = s.fs.files) : FsAt envOk Q P s' := by
  rcases h with h | ⟨hQ, hP, he⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, hf ▸ he⟩

theorem FsAt.of_steps {envOk : FsFiles → Prop} {Q : Prop} {P : Program} {s s' : State}
    (h : FsAt envOk Q P s) (hst : Steps P s s') {evs : List TraceEvent}
    (htr : s'.trace = s.trace ++ evs) (hq : Q → NoFsEv evs) : FsAt envOk Q P s' := by
  rcases h with h | ⟨hQ, hP, he⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, (hP.files_eq hst htr (hq hQ)) ▸ he⟩

theorem FsAt.of_call {envOk : FsFiles → Prop} {Q : Prop} {P : Program} {s sc sf : State}
    (h : FsAt envOk Q P s) (hst : Steps P sc sf) (hf : sc.fs.files = s.fs.files)
    (htr : sf.trace = sc.trace) : FsAt envOk Q P sf :=
  (h.of_files_eq hf).of_steps hst (evs := []) (by rw [htr, List.append_nil])
    (fun _ => NoFsEv.nil)

theorem FsCtx.fsAt {envOk : FsFiles → Prop} {Q : Prop} {P : Program} {s0 s : State}
    (h : FsCtx envOk Q P s0 s) {evs : List TraceEvent} (htr : s.trace = s0.trace ++ evs)
    (hq : Q → NoFsEv evs) : FsAt envOk Q P s := by
  have he := h.envOk_at htr hq
  rcases h with h | ⟨hQ, hP, -, -⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, he⟩

theorem FsAt.mono {e₁ e₂ : FsFiles → Prop} {Q₁ Q₂ : Prop} {P : Program} {s : State}
    (he : ∀ f, e₁ f → e₂ f) (hQ : Q₁ → Q₂) (h : FsAt e₁ Q₁ P s) : FsAt e₂ Q₂ P s := by
  rcases h with h | ⟨hq, hP, h0⟩
  · exact .inl fun f => he f (h f)
  · exact .inr ⟨hQ hq, hP, he _ h0⟩

/-! ## Postcondition Step Recording (`withStepsPost`) -/

/-- Augments `spec` with `⌜Steps prog s0 sf⌝` in its postcondition. -/
abbrev withStepsPost {α : Type} (prog : Program) (spec : Spec α) : Spec α :=
  Arm64.ReachesOutcome.withStepsPost prog spec

theorem subroutine_ok_withStepsPost {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withStepsPost prog spec) :=
  Arm64.ReachesOutcome.subroutine_ok_withStepsPost h

/-! ## Precondition Environment Guard (`withEnvPre`) -/

/-- Conjoins pure state predicate `φ` to `spec.pre`. -/
def withEnvPre {α : Type} (spec : Spec α) (φ : State → Prop) : Spec α :=
  { spec with pre := fun x s => ⌜φ s⌝ ∗ spec.pre x s }

@[simp] theorem withEnvPre_post {α : Type} (spec : Spec α) (φ : State → Prop) :
    (withEnvPre spec φ).post = spec.post := rfl
@[simp] theorem withEnvPre_onPanic {α : Type} (spec : Spec α) (φ : State → Prop) :
    (withEnvPre spec φ).onPanic = spec.onPanic := rfl
@[simp] theorem withEnvPre_onExit {α : Type} (spec : Spec α) (φ : State → Prop) :
    (withEnvPre spec φ).onExit = spec.onExit := rfl
@[simp] theorem withEnvPre_onOom {α : Type} (spec : Spec α) (φ : State → Prop) :
    (withEnvPre spec φ).onOom = spec.onOom := rfl

theorem reaches_outcome_withEnvPre {α : Type} {prog : Program} {spec : Spec α} {φ : State → Prop}
    {x : α} {R : SepProp} {s0 s : State} :
    reaches_outcome prog (withEnvPre spec φ) x R s0 s ↔ reaches_outcome prog spec x R s0 s :=
  ⟨fun h => h.mono_outcome (fun _ hout => hout), fun h => h.mono_outcome (fun _ hout => hout)⟩

theorem withEnvPre_pre_intro {α : Type} {spec : Spec α} {φ : State → Prop} {x : α} {s : State}
    {R : SepProp} (hφ : φ s) (h : s.mem ⊨ spec.pre x s ∗ R) :
    s.mem ⊨ (withEnvPre spec φ).pre x s ∗ R := by
  show s.mem ⊨ (⌜φ s⌝ ∗ spec.pre x s) ∗ R
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hφ, h⟩

theorem withEnvPre_pre_elim {α : Type} {spec : Spec α} {φ : State → Prop} {x : α} {s : State}
    {R : SepProp} (h : s.mem ⊨ (withEnvPre spec φ).pre x s ∗ R) :
    φ s ∧ (s.mem ⊨ spec.pre x s ∗ R) := by
  change s.mem ⊨ (⌜φ s⌝ ∗ spec.pre x s) ∗ R at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h

theorem subroutine_ok_withEnvPre {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) (φ : State → Prop) :
    subroutine_ok prog entry (withEnvPre spec φ) :=
  subroutine_ok_mono h (fun _ _ _ hp => (withEnvPre_pre_elim hp).2)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

theorem subroutine_ok_of_withEnvPre {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {φ : State → Prop} (h : subroutine_ok prog entry (withEnvPre spec φ))
    (hφ : ∀ s, φ s) : subroutine_ok prog entry spec :=
  subroutine_ok_mono h (fun _ _ s hp => withEnvPre_pre_intro (hφ s) hp)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

end CryptoVerification.LibsignalPublicApi.StoreKit
