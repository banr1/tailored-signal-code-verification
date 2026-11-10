/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire

@[expose] public section
namespace Symbolic.BugInjection.Proofs.Common443.CompFitsNames
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp
variable {w : PQXDHSpqrSetup} {i : ExternInterpretation} {r : Records}
theorem compFits_base (h : compFitsPinned w i r) : compFits w i r := h.1
theorem compFits_alice (h : compFitsPinned w i r) : r.alice = "alice" := h.2.2.2.1.1
theorem compFits_bob (h : compFitsPinned w i r) : r.bob = "bob" := h.2.2.2.1.2
theorem compFits_secretBytes_fresh (h : compFitsPinned w i r) : secretBytes r 3 = fillFresh 11 64 ∧ secretBytes r 4 = fillFresh 16 64 ∧ secretBytes r 5 = fillFresh 17 64 := h.2.2.1

def checkPreKeyOuter (w : PQXDHSpqrSetup) (i : ExternInterpretation) (b : HwBytes) : Bool :=
  match parsePreKeyWire b with
  | none => false
  | some q =>
    decide (q.version = 4) && decide (q.signedPreKeyId = w.spkId) &&
      decide (q.kyberPreKeyId = some w.kpkId) &&
      decide (q.identityKey.take 33 = ecKey (pubBytes i w.aliceId)) &&
      decide (q.preKeyId = none)

theorem preKeyOuterMatches_of_check {w : PQXDHSpqrSetup} {i : ExternInterpretation} {r : Records}
    {b : HwBytes} {q : PreKeyFields} (hf : compFits w i r) (hq : parsePreKeyWire b = some q)
    (h : checkPreKeyOuter w i b = true) :
    Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire.PreKeyOuterMatches i r b q := by
  unfold checkPreKeyOuter at h; rw [hq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, _, _, _, hspk, hkpk, haid, _⟩ := hf
  refine ⟨h.1.1.1.1, h.1.1.1.2.trans hspk.symm, h.1.1.2.trans (congrArg some hkpk.symm), ?_, ⟨false, q, hq, h.2⟩⟩
  rw [haid]; exact h.1.2

end Symbolic.BugInjection.Proofs.Common443.CompFitsNames
