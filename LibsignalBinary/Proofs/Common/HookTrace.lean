/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic

/-!
# Trace-Preserving `HookOk` Spec Lifting

Provides `HookOk.of_trace` to lift an engine `HookOk f spec` witness to a strengthened `spec'` when
`f` preserves `State.trace`.
-/

@[expose] public section

namespace CryptoVerification.HookTrace

open Arm64 ProofLib

/-- Lift an engine `HookOk f spec` witness to `HookOk f spec'` when `spec'.pre` entails `spec.pre`,
    `f` preserves `trace`, and `spec.post` together with `sf.trace = s0.trace` establishes
    `spec'.post` (passing panic and exit outcomes through). -/
theorem HookOk.of_trace {α : Type} {f : State → State} {spec spec' : Spec α}
    (hok : HookOk f spec)
    (hpost : ∀ x R s0, (f s0).trace = s0.trace →
      ((f s0).mem ⊨ spec.post x s0 (f s0) ∗ R) → ((f s0).mem ⊨ spec'.post x s0 (f s0) ∗ R))
    (hpre : ∀ x R s0, (s0.mem ⊨ spec'.pre x s0 ∗ R) → (s0.mem ⊨ spec.pre x s0 ∗ R) := by
      intro _ _ _ h; exact h)
    (htrace : ∀ s0, (f s0).trace = s0.trace := by intro _; rfl)
    (hpanic : ∀ x R s0 sf,
      (sf.mem ⊨ spec.onPanic x s0 sf ∗ R) → (sf.mem ⊨ spec'.onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ h; exact h)
    (hexit : ∀ x code R s0 sf,
      (sf.mem ⊨ spec.onExit x code s0 sf ∗ R) → (sf.mem ⊨ spec'.onExit x code s0 sf ∗ R) := by
      intro _ _ _ _ _ h; exact h)
    (hoom : ∀ x R s0 sf,
      (sf.mem ⊨ spec.onOom x s0 sf ∗ R) → (sf.mem ⊨ spec'.onOom x s0 sf ∗ R) := by
      intro _ _ _ _ h; exact h) :
    HookOk f spec' := by
  intro x R s0 hrun hp hsp
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun (hpre x R s0 hp) hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨ho, hq⟩
  · exact Or.inl ⟨hret, hcc, hpost x R s0 (htrace s0) hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hpanic x R s0 (f s0) hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hexit x code R s0 (f s0) hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom x R s0 (f s0) hq⟩))

end CryptoVerification.HookTrace
