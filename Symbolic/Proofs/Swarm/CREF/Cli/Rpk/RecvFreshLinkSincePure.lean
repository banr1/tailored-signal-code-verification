/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.Instance
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvFreshLinkPureA
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec -- shake: keep

/-!
# Receiver-Key Absence Lemma

Shows `receiverKeyUsedB tr s seed n r = false` when no `TREvent.MessageKey` event
with direction `.receiver` and seed `seed` appears on `tr`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession
open DY.Libsignal.TripleRatchet (SessionInfo)
open DY.Libsignal.TripleRatchet (TREvent receiverKeyUsedB)
open Symbolic.Swarm.CREF.TR.RecvDec
  (StEntry TREntry at?_append_of_lt at?_eq_none_of_le at?_append_non_entry
   logSkippedKeysTr logSkippedKeysTr_length at?_trEntry_logSkippedKeysTr_lt
   at?_trEntry_logSkippedKeysTr_add decTailTr decSkippedTr decRatchetPreTr trDhRatchetState)

theorem receiverKeyUsedB_false_of_no_messageKey_tr {tr : ExecTrace} {s : SessionInfo} {seed : DY.Bytes}
    (hno : ∀ pqSalt n r pIdx i,
      ¬ tr.EventLoggedAt (TREvent.MessageKey s .receiver seed pqSalt n r pIdx) i)
    (n : UInt32) (r : Nat) :
    receiverKeyUsedB tr s seed n r = false := by
  rcases hb : receiverKeyUsedB tr s seed n r with _ | _
  · rfl
  · exfalso; unfold receiverKeyUsedB at hb
    obtain ⟨ev, i, hev, hq⟩ := exists_eventLoggedAt_of_someEventOnTraceB_tr hb
    cases ev with
    | MessageKey s' dir seed' pqSalt' n' r' pa' =>
      cases dir with
      | receiver =>
        simp only [decide_eq_true_eq] at hq; obtain ⟨hs, hseed, hn_eq, hr_eq⟩ := hq
        subst hs hseed hn_eq hr_eq
        exact hno pqSalt' n' r' pa' i hev
      | sender => simp at hq
    | _ => simp at hq

end Symbolic.Swarm.CREF.CliPure.TR
