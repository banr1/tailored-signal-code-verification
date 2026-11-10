/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Fs

/-!
# File-Descriptor-Carrying StoreKit Contexts (`FsCtxFds`, `FsAtFds`)

Variants of `FsCtx` and `FsAt` whose `.inr` branch additionally threads a pointwise file-descriptor
invariant `fdsOk s.fs` (such as `FdsGe3Closed` for CLI file-backed store kits).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.FsFds

open Arm64
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsAt FsCtx FsFiles KitFsOk NoFsEv TraceFsSound)

/-- Entry-to-current file-system and file-descriptor context threading `fdsOk s.fs` in `.inr`. -/
def FsCtxFds (envOk : FsFiles → Prop) (fdsOk : FsState → Prop) (Q : Prop) (P : Program)
    (s0 s : State) : Prop :=
  (∀ f, envOk f) ∨ (Q ∧ TraceFsSound P ∧ envOk s0.fs.files ∧ Steps P s0 s ∧ fdsOk s.fs)

theorem FsCtxFds.toFsCtx {envOk : FsFiles → Prop} {fdsOk : FsState → Prop} {Q : Prop}
    {P : Program} {s0 s : State} (h : FsCtxFds envOk fdsOk Q P s0 s) :
    FsCtx envOk Q P s0 s := by
  rcases h with h | ⟨hQ, hP, h0, hr, -⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, h0, hr⟩

theorem FsCtxFds.of_entry {envOk : FsFiles → Prop} {fdsOk : FsState → Prop} {Q : Prop}
    {P : Program} {s0 : State}
    (h : KitFsOk envOk Q P) (h0 : envOk s0.fs.files) (hfds0 : fdsOk s0.fs) :
    FsCtxFds envOk fdsOk Q P s0 s0 := by
  rcases h with h | ⟨hQ, hP⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, h0, Steps.refl s0, hfds0⟩

theorem FsCtxFds.of_steps {envOk : FsFiles → Prop} {fdsOk : FsState → Prop} {Q : Prop}
    {P : Program} {s0 s s' : State}
    (h : FsCtxFds envOk fdsOk Q P s0 s) (hst : Steps P s s') (hfds : fdsOk s'.fs) :
    FsCtxFds envOk fdsOk Q P s0 s' := by
  rcases h with h | ⟨hQ, hP, h0, hr, -⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, h0, hr.trans hst, hfds⟩

theorem FsCtxFds.of_fs_eq {envOk : FsFiles → Prop} {fdsOk : FsState → Prop} {Q : Prop}
    {P : Program} {s0 s s' : State}
    (h : FsCtxFds envOk fdsOk Q P s0 s) (hst : Steps P s s') (hfs : s'.fs = s.fs) :
    FsCtxFds envOk fdsOk Q P s0 s' := by
  rcases h with h | ⟨hQ, hP, h0, hr, hfds⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, h0, hr.trans hst, hfs ▸ hfds⟩

theorem FsCtxFds.envOk_at {envOk : FsFiles → Prop} {fdsOk : FsState → Prop} {Q : Prop}
    {P : Program} {s0 s : State}
    (h : FsCtxFds envOk fdsOk Q P s0 s) {evs : List TraceEvent} (htr : s.trace = s0.trace ++ evs)
    (hq : Q → NoFsEv evs) : envOk s.fs.files :=
  h.toFsCtx.envOk_at htr hq

theorem FsCtxFds.fdsOk_at {envOk : FsFiles → Prop} {fdsOk : FsState → Prop} {Q : Prop}
    {P : Program} {s0 s : State}
    (h : FsCtxFds envOk fdsOk Q P s0 s)
    (htriv : (∀ f, envOk f) → fdsOk s.fs) : fdsOk s.fs := by
  rcases h with h | ⟨-, -, -, -, hfds⟩
  · exact htriv h
  · exact hfds

theorem FsCtxFds.rebase {envOk : FsFiles → Prop} {fdsOk : FsState → Prop} {Q : Prop}
    {P : Program} {s0 s : State}
    (h : FsCtxFds envOk fdsOk Q P s0 s) {evs : List TraceEvent} (htr : s.trace = s0.trace ++ evs)
    (hq : Q → NoFsEv evs) : FsCtxFds envOk fdsOk Q P s s := by
  have he := h.envOk_at htr hq
  rcases h with h | ⟨hQ, hP, -, -, hfds⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, he, Steps.refl s, hfds⟩

theorem FsCtxFds.mono {e₁ e₂ : FsFiles → Prop} {f₁ f₂ : FsState → Prop} {Q₁ Q₂ : Prop}
    {P : Program} {s0 s : State}
    (he : ∀ f, e₁ f → e₂ f) (hfds : ∀ fs, f₁ fs → f₂ fs) (hQ : Q₁ → Q₂)
    (h : FsCtxFds e₁ f₁ Q₁ P s0 s) : FsCtxFds e₂ f₂ Q₂ P s0 s := by
  rcases h with h | ⟨hq, hP, h0, hr, hf⟩
  · exact .inl fun f => he f (h f)
  · exact .inr ⟨hQ hq, hP, he _ h0, hr, hfds _ hf⟩

/-- Pointwise file-system and file-descriptor carrier threading `fdsOk s.fs` in `.inr`. -/
def FsAtFds (envOk : FsFiles → Prop) (fdsOk : FsState → Prop) (Q : Prop) (P : Program)
    (s : State) : Prop :=
  (∀ f, envOk f) ∨ (Q ∧ TraceFsSound P ∧ envOk s.fs.files ∧ fdsOk s.fs)

theorem FsAtFds.toFsAt {envOk : FsFiles → Prop} {fdsOk : FsState → Prop} {Q : Prop}
    {P : Program} {s : State} (h : FsAtFds envOk fdsOk Q P s) : FsAt envOk Q P s := by
  rcases h with h | ⟨hQ, hP, he, -⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, he⟩

theorem FsAtFds.envOk_here {envOk : FsFiles → Prop} {fdsOk : FsState → Prop} {Q : Prop}
    {P : Program} {s : State} (h : FsAtFds envOk fdsOk Q P s) : envOk s.fs.files :=
  h.toFsAt.envOk_here

theorem FsAtFds.fdsOk_here {envOk : FsFiles → Prop} {fdsOk : FsState → Prop} {Q : Prop}
    {P : Program} {s : State} (h : FsAtFds envOk fdsOk Q P s)
    (htriv : (∀ f, envOk f) → fdsOk s.fs) : fdsOk s.fs := by
  rcases h with h | ⟨-, -, -, hfds⟩
  · exact htriv h
  · exact hfds

theorem FsAtFds.of_files_eq {envOk : FsFiles → Prop} {fdsOk : FsState → Prop} {Q : Prop}
    {P : Program} {s s' : State}
    (h : FsAtFds envOk fdsOk Q P s) (hf : s'.fs.files = s.fs.files) (hfds : fdsOk s'.fs) :
    FsAtFds envOk fdsOk Q P s' := by
  rcases h with h | ⟨hQ, hP, he, -⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, hf ▸ he, hfds⟩

theorem FsAtFds.of_fs_eq {envOk : FsFiles → Prop} {fdsOk : FsState → Prop} {Q : Prop}
    {P : Program} {s s' : State}
    (h : FsAtFds envOk fdsOk Q P s) (hfs : s'.fs = s.fs) :
    FsAtFds envOk fdsOk Q P s' := by
  rcases h with h | ⟨hQ, hP, he, hfds⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, (congrArg FsState.files hfs) ▸ he, hfs ▸ hfds⟩

theorem FsAtFds.of_steps {envOk : FsFiles → Prop} {fdsOk : FsState → Prop} {Q : Prop}
    {P : Program} {s s' : State}
    (h : FsAtFds envOk fdsOk Q P s) (hst : Steps P s s') {evs : List TraceEvent}
    (htr : s'.trace = s.trace ++ evs) (hq : Q → NoFsEv evs) (hfds : fdsOk s'.fs) :
    FsAtFds envOk fdsOk Q P s' := by
  rcases h with h | ⟨hQ, hP, he, -⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, (hP.files_eq hst htr (hq hQ)) ▸ he, hfds⟩

theorem FsAtFds.of_call {envOk : FsFiles → Prop} {fdsOk : FsState → Prop} {Q : Prop}
    {P : Program} {s sc sf : State}
    (h : FsAtFds envOk fdsOk Q P s) (hst : Steps P sc sf) (hf : sc.fs.files = s.fs.files)
    (htr : sf.trace = sc.trace) (hfds : fdsOk sf.fs) :
    FsAtFds envOk fdsOk Q P sf := by
  rcases h with h | ⟨hQ, hP, he, -⟩
  · exact .inl h
  · have hsc : envOk sc.fs.files := hf ▸ he
    have hsf : sf.fs.files = sc.fs.files :=
      hP.files_eq hst (evs := []) (by rw [htr, List.append_nil]) NoFsEv.nil
    exact .inr ⟨hQ, hP, hsf ▸ hsc, hfds⟩

theorem FsCtxFds.fsAt {envOk : FsFiles → Prop} {fdsOk : FsState → Prop} {Q : Prop}
    {P : Program} {s0 s : State}
    (h : FsCtxFds envOk fdsOk Q P s0 s) {evs : List TraceEvent} (htr : s.trace = s0.trace ++ evs)
    (hq : Q → NoFsEv evs) : FsAtFds envOk fdsOk Q P s := by
  have he := h.envOk_at htr hq
  rcases h with h | ⟨hQ, hP, -, -, hfds⟩
  · exact .inl h
  · exact .inr ⟨hQ, hP, he, hfds⟩

theorem FsAtFds.mono {e₁ e₂ : FsFiles → Prop} {f₁ f₂ : FsState → Prop} {Q₁ Q₂ : Prop}
    {P : Program} {s : State}
    (he : ∀ f, e₁ f → e₂ f) (hfds : ∀ fs, f₁ fs → f₂ fs) (hQ : Q₁ → Q₂)
    (h : FsAtFds e₁ f₁ Q₁ P s) : FsAtFds e₂ f₂ Q₂ P s := by
  rcases h with h | ⟨hq, hP, h0, hf⟩
  · exact .inl fun f => he f (h f)
  · exact .inr ⟨hQ hq, hP, he _ h0, hfds _ hf⟩

end LibsignalBinary.Proofs.PublicApi.StoreKit.FsFds
