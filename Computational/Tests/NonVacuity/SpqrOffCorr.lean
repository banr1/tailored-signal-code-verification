/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.State
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalWireRoundTrip

/-!
# SPQR-Off Correctness Hypotheses

Verifies that the disabled-SPQR hook bundle `spqrOffB` satisfies `Corr.SpqrSendTotalReachable` and
`Corr.SpqrRecvSaltFixed`.
-/

@[expose] public section

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSM

/-- `spqrOffB.send` always returns `some ([], none, [])` with `sendPanics = false`. -/
theorem spqrSendTotalReachable_spqrOffB : Corr.SpqrSendTotalReachable spqrOffB := by
  intro _ _ _ _ _
  exact ⟨rfl, rfl⟩

/-- `spqrOffB.recv` always returns `salt = none` on success. -/
theorem spqrRecvSaltFixed_spqrOffB : Corr.SpqrRecvSaltFixed spqrOffB := by
  refine ⟨fun _ _ => True, fun _ _ => none, fun _ _ _ _ _ _ _ => trivial, ?_⟩
  intro st st' st'' msg salt _ _ h
  simp only [spqrOffB, CryptoVerification.LibsignalSpqr.spqrRecvEmpty] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  · simp at h

end CryptoVerification.E2E
